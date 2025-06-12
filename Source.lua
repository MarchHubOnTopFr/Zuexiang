--[[
  Zuexiang (祖翔)
  A fork of the Yueliang Lua 5.1 compiler, with extended features and optimizations.

  Original base project:
    Yueliang - Lua 5.1 Bytecode Compiler
    Author: Kein-Hong Man
    Source: http://yueliang.luaforge.net/

  Modifications and extensions by:
    Nyreel

  This version includes:
    - Support for 'goto' and 'continue'
    - Compound assignment (+=, -=, etc.) with proper table/index handling
    - '!=' alias for '~='
    - Luau-style number literals (binary, octal, hex, 1_000, 1e3, etc.)
    - Ternary expressions in local declarations
    - Integer division operator (//)
    - Type annotation, type assertion, and type definitions (parser-only)
    - Parsing support for <const> and <close> variable qualifiers
    - Renamed local names for better readability
    - Parser and performance improvements

  License:
    MIT License (same as original Yueliang)

  Note:
    This is not an official continuation of Yueliang. It’s a personal project made
    for experimentation, learning, and fun. Expect messy code and fast hacks.
]]

local Buffer, Parser, Lexer, Serializer, Codegen = {}, {}, {}, {}, {}
function Buffer:init(source)
    local pos, buffer = 1, ""
    return {reader = function()
            if pos > #source and #buffer == 0 then
                return nil
            end
            if #buffer == 0 then
                buffer = source:sub(pos, pos + 4095)
                pos = pos + #buffer
            end
            local c = buffer:sub(1, 1)
            buffer = buffer:sub(2)
            return c
        end, data = "", name = "", n = 0, p = 0}
end
function Buffer:fill(z)
    z.data = z.reader() or ""
    z.n, z.p = #z.data - 1, 1
    return z.n >= 0 and z.data:sub(1, 1) or "EOZ"
end
Lexer.RESERVED =
    [[
    TK_AND and
    TK_BREAK break
    TK_CONTINUE continue
    TK_DO do
    TK_ELSE else
    TK_ELSEIF elseif
    TK_END end
    TK_FALSE false
    TK_FOR for
    TK_FUNCTION function
    TK_GOTO goto
    TK_IF if
    TK_IN in
    TK_LOCAL local
    TK_NIL nil
    TK_NOT not
    TK_OR or
    TK_REPEAT repeat
    TK_RETURN return
    TK_THEN then
    TK_TRUE true
    TK_UNTIL until
    TK_WHILE while
    TK_CONCAT ..
    TK_DOTS ...
    TK_EQ ==
    TK_GE >=
    TK_LE <=
    TK_NE ~=
    TK_NE2 !=
    TK_ADD2 +=
    TK_SUB2 -=
    TK_MUL2 *=
    TK_DIV2 /=
    TK_MOD2 %=
    TK_POW2 ^=
    TK_CONCAT2 ..=
    TK_FLOORDIV //
    TK_FLOORDIV2 //=
    TK_DOUBLECOLON ::
    TK_VAL --disabledval
    TK_NAME <name>
    TK_NUMBER <number>
    TK_STRING <string>
    TK_EOS <eof>
]]
Lexer.MAXSRC = 80
Lexer.MAX_INT = 2147483645
Lexer.LUA_COMPAT_LSTR = 1
function Lexer:init()
    local tokens, enums = {}, {}
    for tok, str in self.RESERVED:gmatch("(%S+)%s+(%S+)") do
        tokens[tok], enums[str] = str, tok
    end
    self.tokens, self.enums = tokens, enums
end
function Lexer:chunkid(source, bufflen)
    local first, len = source:sub(1, 1), bufflen - 3
    if first == "=" then
        return source:sub(2, len + 1)
    end
    source = first == "@" and source:sub(2) or source:sub(1, (source:find("[\n\r]") or #source + 1) - 1)
    len = math.min(len + 1, #source)
    source = #source > len and "..." .. source:sub(-len) or ('[string "%s"]'):format(source)
    return source
end
function Lexer:token2str(token)
    local t = self.tokens[token]
    return t or type(token) == string and (token:match("%c") and ("char(%d)"):format(token:byte())) or token
end
function Lexer:lexerror(ls, msg, token)
    local txtToken =
        (token == "TK_NAME" or token == "TK_STRING" or token == "TK_NUMBER") and ls.buff or self:token2str(token) or
        "<unknown>"
    local line, context = ls.linenumber, ls.buff or ls.current or "<unknown>"
    error(
        ("%s:%d: %s (near '%s')%s"):format(
            self:chunkid(ls.source, self.MAXSRC),
            line,
            msg,
            context,
            token and ", token: " .. txtToken
        )
    )
end
function Lexer:syntaxerror(ls, msg)
    self:lexerror(ls, msg, ls.t.token)
end
function Lexer:currIsNewline(ls)
    return ls.current == "\n" or ls.current == "\r"
end
function Lexer:inclinenumber(ls)
    local old = ls.current
    self:nextc(ls)
    if self:currIsNewline(ls) and ls.current ~= old then
        self:nextc(ls)
    end
    ls.linenumber = ls.linenumber + 1
    if ls.linenumber >= self.MAX_INT then
        self:syntaxerror(ls, "chunk has too many lines")
    end
end
function Lexer:setinput(L, ls, z, source)
    ls = ls or {}
    ls.lookahead, ls.t = ls.lookahead or {}, ls.t or {}
    ls.decpoint, ls.L = ".", L
    ls.lookahead.token = "TK_EOS"
    ls.z, ls.fs = z, nil
    ls.linenumber, ls.lastline = 1, 1
    ls.source = source
    self:nextc(ls)
end
function Lexer:check_next(ls, set)
    if not set:find(ls.current, 1, true) then
        return false
    end
    self:save_and_next(ls)
    return true
end
function Lexer:next(ls)
    ls.lastline = ls.linenumber
    if ls.lookahead.token ~= "TK_EOS" then
        ls.t.token, ls.t.seminfo = ls.lookahead.token, ls.lookahead.seminfo
        ls.lookahead.token = "TK_EOS"
    else
        ls.t.token = self:llex(ls, ls.t)
    end
end
function Lexer:lookahead(ls)
    ls.lookahead.token = self:llex(ls, ls.lookahead)
end
function Lexer:nextc(ls)
    local z = ls.z
    z.p = z.p + 1
    z.n = z.n - 1
    if z.n > 0 then
        ls.current = z.data:sub(z.p, z.p)
    else
        z.data = z.reader() or ""
        z.n, z.p = #z.data - 1, 1
        ls.current = z.n >= 0 and z.data:sub(1, 1) or "EOZ"
    end
    return ls.current
end
function Lexer:save(ls, c)
    ls.buff = (ls.buff or "") .. c
end
function Lexer:save_and_next(ls)
    ls.buff = (ls.buff or "") .. ls.current
    local z = ls.z
    z.p = z.p + 1
    z.n = z.n - 1
    if z.n > 0 then
        ls.current = z.data:sub(z.p, z.p)
    else
        z.data = z.reader() or ""
        z.n, z.p = #z.data - 1, 1
        ls.current = z.n >= 0 and z.data:sub(1, 1) or "EOZ"
    end
    return ls.current
end
function Lexer:buffreplace(ls, from, to)
    local result, buff = "", ls.buff
    for p = 1, #buff do
        local c = string.sub(buff, p, p)
        if c == from then
            c = to
        end
        result = result .. c
    end
    ls.buff = result
end
function Lexer:trydecpoint(ls, Token)
    local old = ls.decpoint
    self:buffreplace(ls, old, ".")
    self:buffreplace(ls, "_", "")
    local s = ls.buff
    local num = tonumber(s)
    if not num then
        self:lexerror(ls, "malformed number", "TK_NUMBER")
    end
    Token.seminfo = num
end
function Lexer:read_numeral(ls, Token)
    local buffer = {}
    local is_hex, is_bin, is_oct = false, false, false
    local neg = false
    if ls.current == "-" then
        neg = true
        self:nextc(ls)
    end
    if ls.current == "0" then
        buffer[#buffer + 1] = ls.current
        self:nextc(ls)
        local c = ls.current:lower()
        if c == "x" then
            is_hex = true
            buffer[#buffer + 1] = c
            self:nextc(ls)
        elseif c == "b" then
            is_bin = true
            buffer[#buffer + 1] = c
            self:nextc(ls)
        elseif c == "o" then
            is_oct = true
            buffer[#buffer + 1] = c
            self:nextc(ls)
        end
    end
    local pat = is_hex and "[0-9a-fA-F_]" or is_bin and "[01_]" or is_oct and "[0-7_]" or "[0-9_]"
    local seen_dot, seen_exp = false, false
    while true do
        local ch = ls.current
        if ch:match(pat) then
            buffer[#buffer + 1] = ch
            self:nextc(ls)
        elseif ch == "." and not (seen_dot or is_bin or is_oct) then
            seen_dot = true
            buffer[#buffer + 1] = ch
            self:nextc(ls)
        elseif (ch == "e" or ch == "E") and not seen_exp and not (is_hex or is_bin or is_oct) then
            seen_exp = true
            buffer[#buffer + 1] = ch
            self:nextc(ls)
            if ls.current == "+" or ls.current == "-" then
                buffer[#buffer + 1] = ls.current
                self:nextc(ls)
            end
        elseif (ch == "p" or ch == "P") and is_hex and not seen_exp then
            seen_exp = true
            buffer[#buffer + 1] = ch
            self:nextc(ls)
            if ls.current == "+" or ls.current == "-" then
                buffer[#buffer + 1] = ls.current
                self:nextc(ls)
            end
        else
            break
        end
    end
    local s = table.concat(buffer):gsub("_", "")
    local num
    if is_hex then
        local intp, fracp, exp = s:match("^0[xX]([0-9A-Fa-f]*)%.?([0-9A-Fa-f]*)[pP]?([%+%-]?%d*)")
        if not intp then
            self:lexerror(ls, "malformed hexadecimal", "TK_NUMBER")
        end
        intp = intp == "" and "0" or intp
        local v = 0
        for d in intp:gmatch(".") do
            v = v * 16 + tonumber(d, 16)
        end
        if fracp and #fracp > 0 then
            local div = 16
            for d in fracp:gmatch(".") do
                v = v + tonumber(d, 16) / div
                div = div * 16
            end
        end
        local e = tonumber(exp) or 0
        num = v * 2 ^ e
    elseif is_bin then
        num = tonumber(s:match("^0[bB]([01]+)$") or s, 2)
    elseif is_oct then
        num = tonumber(s:match("^0[oO]([0-7]+)$") or s, 8)
    else
        self:buffreplace(ls, ls.decpoint, ".")
        num = tonumber(s)
    end
    if not num then
        self:lexerror(ls, "malformed number", "TK_NUMBER")
    end
    Token.seminfo = neg and -num or num
end
function Lexer:read_long_string(ls, Token, sep)
    local cont = 0
    self:save_and_next(ls)
    if self:currIsNewline(ls) then
        self:inclinenumber(ls)
    end
    while true do
        local c = ls.current
        if c == "EOZ" then
            self:lexerror(ls, Token and "unfinished long string" or "unfinished long comment", "TK_EOS")
        elseif c == "[" and self.LUA_COMPAT_LSTR then
            if self:skip_sep(ls) == sep then
                self:save_and_next(ls)
                cont = cont + 1
                if self.LUA_COMPAT_LSTR == 1 and sep == 0 then
                    self:lexerror(ls, "nesting of [[...]] is deprecated", "[")
                end
            end
        elseif c == "]" then
            if self:skip_sep(ls) == sep then
                self:save_and_next(ls)
                if self.LUA_COMPAT_LSTR == 2 then
                    cont = cont - 1
                    if sep == 0 and cont >= 0 then
                        break
                    end
                end
                break
            end
        elseif self:currIsNewline(ls) then
            self:save(ls, "\n")
            self:inclinenumber(ls)
            if not Token then
                ls.buff = ""
            end
        else
            if Token then
                self:save_and_next(ls)
            else
                self:nextc(ls)
            end
        end
    end
    if Token then
        Token.seminfo = ls.buff:sub(3 + sep, -(3 + sep))
    end
end
function Lexer:read_string(ls, del, Token)
    self:save_and_next(ls)
    while ls.current ~= del do
        local c = ls.current
        if c == "EOZ" or self:currIsNewline(ls) then
            self:lexerror(ls, "unfinished string", c == "EOZ" and "TK_EOS" or "TK_STRING")
        end
        if c == "\\" then
            c = self:nextc(ls)
            if self:currIsNewline(ls) then
                self:save(ls, "\n")
                self:inclinenumber(ls)
            elseif c ~= "EOZ" then
                local i = ("abfnrtv"):find(c, 1, true)
                if i then
                    self:save(ls, ("\a\b\f\n\r\t\v"):sub(i, i))
                    self:nextc(ls)
                elseif not c:find("%d") then
                    self:save_and_next(ls)
                else
                    local num, i = 0, 0
                    repeat
                        num, i, c = num * 10 + tonumber(c), i + 1, self:nextc(ls)
                    until i >= 3 or not c:find("%d")
                    if num > 255 then
                        self:lexerror(ls, "escape sequence too large", "TK_STRING")
                    end
                    self:save(ls, string.char(num))
                end
            end
        else
            self:save_and_next(ls)
        end
    end
    self:save_and_next(ls)
    Token.seminfo = ls.buff:sub(2, -2)
end
function Lexer:skip_sep(ls)
    local count = 0
    local s = ls.current
    self:save_and_next(ls)
    while ls.current == "=" do
        self:save_and_next(ls)
        count = count + 1
    end
    return (ls.current == s) and count or (-count) - 1
end
function Lexer:llex(ls, Token)
    ls.buff = ""
    while true do
        local c = ls.current
        if self:currIsNewline(ls) then
            self:inclinenumber(ls)
        elseif c == "-" then
            c = self:nextc(ls)
            if c == "-" then
                local sep = -1
                if self:nextc(ls) == "[" then
                    sep = self:skip_sep(ls)
                    ls.buff = ""
                end
                if sep >= 0 then
                    self:read_long_string(ls, nil, sep)
                    ls.buff = ""
                else
                    while not self:currIsNewline(ls) and ls.current ~= "EOZ" do
                        self:nextc(ls)
                    end
                end
            elseif c == "=" then
                self:nextc(ls)
                return "TK_SUB2"
            else
                return "-"
            end
        elseif c == "+" then
            c = self:nextc(ls)
            if c == "=" then
                self:nextc(ls)
                return "TK_ADD2"
            else
                return "+"
            end
        elseif c == "*" then
            c = self:nextc(ls)
            if c == "=" then
                self:nextc(ls)
                return "TK_MUL2"
            else
                return "*"
            end
        elseif c == "/" then
            c = self:nextc(ls)
            if c == "=" then
                self:nextc(ls)
                return "TK_DIV2"
            elseif c == "/" then
                c = self:nextc(ls)
                if c == "=" then
                    self:nextc(ls)
                    return "TK_FLOORDIV2"
                else
                    ls.current = c
                    return "TK_FLOORDIV"
                end
            else
                return "/"
            end
        elseif c == "%" then
            c = self:nextc(ls)
            if c == "=" then
                self:nextc(ls)
                return "TK_MOD2"
            else
                return "%"
            end
        elseif c == "^" then
            c = self:nextc(ls)
            if c == "=" then
                self:nextc(ls)
                return "TK_POW2"
            else
                return "^"
            end
        elseif c == "." then
            c = self:save_and_next(ls)
            if c == "." then
                c = self:nextc(ls)
                if c == "." then
                    self:nextc(ls)
                    return "TK_DOTS"
                elseif c == "=" then
                    self:nextc(ls)
                    return "TK_CONCAT_ASSIGN"
                else
                    ls.buff = ".."
                    ls.current = c
                    return "TK_CONCAT"
                end
            elseif not string.find(c, "%d") then
                return "."
            else
                self:read_numeral(ls, Token)
                return "TK_NUMBER"
            end
        elseif c == ":" then
            c = self:nextc(ls)
            if c == ":" then
                self:nextc(ls)
                return "TK_DOUBLECOLON"
            else
                return ":"
            end
        elseif c == "[" then
            local sep = self:skip_sep(ls)
            if sep >= 0 then
                self:read_long_string(ls, Token, sep)
                return "TK_STRING"
            elseif sep == -1 then
                return "["
            else
                self:lexerror(ls, "invalid long string delimiter", "TK_STRING")
            end
        elseif c == "=" then
            c = self:nextc(ls)
            if c ~= "=" then
                return "="
            else
                self:nextc(ls)
                return "TK_EQ"
            end
        elseif c == "<" then
            c = self:nextc(ls)
            if c ~= "=" then
                return "<"
            else
                self:nextc(ls)
                return "TK_LE"
            end
        elseif c == ">" then
            c = self:nextc(ls)
            if c ~= "=" then
                return ">"
            else
                self:nextc(ls)
                return "TK_GE"
            end
        elseif c == "~" or c == "!" then
            c = self:nextc(ls)
            if c ~= "=" then
                self:lexerror(ls, "expected '=' after '" .. c .. "'", c)
            else
                self:nextc(ls)
                return "TK_NE"
            end
        elseif c == '"' or c == "'" then
            self:read_string(ls, c, Token)
            return "TK_STRING"
        elseif c == "EOZ" then
            return "TK_EOS"
        else
            if string.find(c, "%s") then
                self:nextc(ls)
            elseif string.find(c, "%d") then
                self:read_numeral(ls, Token)
                return "TK_NUMBER"
            elseif string.find(c, "[_%a]") then
                repeat
                    c = self:save_and_next(ls)
                until c == "EOZ" or not string.find(c, "[_%w]")
                local ts = ls.buff
                local tok = self.enums[ts]
                if tok then
                    return tok
                end
                Token.seminfo = ts
                return "TK_NAME"
            else
                self:nextc(ls)
                return c
            end
        end
    end
end
local floor, char, byte = math.floor, string.char, string.byte
local SIZE_OP, SIZE_A, SIZE_C, SIZE_B = 6, 8, 9, 9
local SIZE_Bx = 18
local POS_OP = 0
local POS_A = 6
local POS_C = 14
local POS_B = 23
local POS_Bx = 14
local MAXARG_A = 255
local MAXARG_B = 511
local MAXARG_C = 511
local MAXARG_Bx = 262143
local MAXARG_sBx = 131071
local BITRK = 256
local MAXINDEXRK = 255
local NO_REG = 255
local Instruction = {
    OpMode = {iABC = 0, iABx = 1, iAsBx = 2},
    SIZE_OP = SIZE_OP,
    SIZE_A = SIZE_A,
    SIZE_C = SIZE_C,
    SIZE_B = SIZE_B,
    SIZE_Bx = SIZE_Bx,
    POS_OP = POS_OP,
    POS_A = POS_A,
    POS_C = POS_C,
    POS_B = POS_B,
    POS_Bx = POS_Bx,
    MAXARG_A = MAXARG_A,
    MAXARG_B = MAXARG_B,
    MAXARG_C = MAXARG_C,
    MAXARG_Bx = MAXARG_Bx,
    MAXARG_sBx = MAXARG_sBx,
    BITRK = BITRK,
    MAXINDEXRK = MAXINDEXRK,
    NO_REG = NO_REG,
    OpArgMask = {OpArgN = 0, OpArgU = 1, OpArgR = 2, OpArgK = 3},
    opnames = {},
    OpCode = {},
    ROpCode = {}
}
local opnames = {
    "MOVE",
    "LOADK",
    "LOADBOOL",
    "LOADNIL",
    "GETUPVAL",
    "GETGLOBAL",
    "GETTABLE",
    "SETGLOBAL",
    "SETUPVAL",
    "SETTABLE",
    "NEWTABLE",
    "SELF",
    "ADD",
    "SUB",
    "MUL",
    "DIV",
    "MOD",
    "POW",
    "UNM",
    "NOT",
    "LEN",
    "CONCAT",
    "JMP",
    "EQ",
    "LT",
    "LE",
    "TEST",
    "TESTSET",
    "CALL",
    "TAILCALL",
    "RETURN",
    "FORLOOP",
    "FORPREP",
    "TFORLOOP",
    "SETLIST",
    "CLOSE",
    "CLOSURE",
    "VARARG"
}
local OpCode, ROpCode, opname = Instruction.OpCode, Instruction.ROpCode, Instruction.opnames
for i = 0, #opnames - 1 do
    local name = "OP_" .. opnames[i + 1]
    opname[i] = opnames[i + 1]
    OpCode[name], ROpCode[i] = i, name
end
Instruction.NUM_OPCODES = #opnames
Instruction.OpArgMask = {OpArgN = 0, OpArgU = 1, OpArgR = 2, OpArgK = 3}
local function opmode(t, a, b, c, m)
    return t * 128 + a * 64 + Instruction.OpArgMask[b] * 16 + Instruction.OpArgMask[c] * 4 + Instruction.OpMode[m]
end
Instruction.opmodes = {
    opmode(0, 1, "OpArgK", "OpArgN", "iABx"),
    opmode(0, 1, "OpArgU", "OpArgU", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgU", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgN", "iABx"),
    opmode(0, 1, "OpArgR", "OpArgK", "iABC"),
    opmode(0, 0, "OpArgK", "OpArgN", "iABx"),
    opmode(0, 0, "OpArgU", "OpArgN", "iABC"),
    opmode(0, 0, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgU", "OpArgU", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgK", "OpArgK", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgR", "iABC"),
    opmode(0, 0, "OpArgR", "OpArgN", "iAsBx"),
    opmode(1, 0, "OpArgK", "OpArgK", "iABC"),
    opmode(1, 0, "OpArgK", "OpArgK", "iABC"),
    opmode(1, 0, "OpArgK", "OpArgK", "iABC"),
    opmode(1, 1, "OpArgR", "OpArgU", "iABC"),
    opmode(1, 1, "OpArgR", "OpArgU", "iABC"),
    opmode(0, 1, "OpArgU", "OpArgU", "iABC"),
    opmode(0, 1, "OpArgU", "OpArgU", "iABC"),
    opmode(0, 0, "OpArgU", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"),
    opmode(0, 1, "OpArgR", "OpArgN", "iAsBx"),
    opmode(1, 0, "OpArgN", "OpArgU", "iABC"),
    opmode(0, 0, "OpArgU", "OpArgU", "iABC"),
    opmode(0, 0, "OpArgN", "OpArgN", "iABC"),
    opmode(0, 1, "OpArgU", "OpArgN", "iABx"),
    opmode(0, 1, "OpArgU", "OpArgN", "iABC")
}
Instruction.opmodes[0] = opmode(0, 1, "OpArgR", "OpArgN", "iABC")
function Instruction:GET_OPCODE(i)
    return self.ROpCode[i.OP]
end
function Instruction:SET_OPCODE(i, o)
    i.OP = self.OpCode[o]
end
function Instruction:GETARG_A(i)
    return i.A
end
function Instruction:SETARG_A(i, a)
    i.A = a
end
function Instruction:GETARG_B(i)
    return i.B
end
function Instruction:SETARG_B(i, b)
    i.B = b
end
function Instruction:GETARG_C(i)
    return i.C
end
function Instruction:SETARG_C(i, c)
    i.C = c
end
function Instruction:GETARG_Bx(i)
    return i.Bx
end
function Instruction:SETARG_Bx(i, bx)
    i.Bx = bx
end
function Instruction:GETARG_sBx(i)
    return i.Bx - self.MAXARG_sBx
end
function Instruction:SETARG_sBx(i, sbx)
    i.Bx = sbx + self.MAXARG_sBx
end
function Instruction:CREATE_ABC(o, a, b, c)
    return {OP = self.OpCode[o], A = a, B = b, C = c}
end
function Instruction:CREATE_ABx(o, a, bc)
    return {OP = self.OpCode[o], A = a, Bx = bc}
end
function Instruction:CREATE_Inst(code)
    local o = code % 64
    local a = (code - o) / 64 % 256
    local bx = (code - o - a * 64) / 16384
    return self:CREATE_ABx(o, a, bx)
end
function Instruction:Instruction(i)
    if i.Bx then
        i.C = i.Bx % 512
        i.B = (i.Bx - i.C) / 512
        assert(i.B < 512, "B argument out of range")
        assert(i.C < 512, "C argument out of range")
    end
    local v = i.A * 64 + i.OP
    assert(i.A < 256, "A argument out of range")
    assert(i.OP < 64, "OP argument out of range")
    local c0 = v % 256
    v = (v - c0) / 256 + i.C * 64
    local c1 = v % 256
    v = (v - c1) / 256 + i.B * 128
    local c2 = v % 256
    local c3 = (v - c2) / 256
    return string.char(c0, c1, c2, c3)
end
function Instruction:DecodeInst(x)
    local byte = string.byte
    local b1, b2, b3, b4 = byte(x, 1, 4)
    local op = b1 % 64
    local a = ((b2 % 256) * 4 + math.floor(b1 / 64)) % 256
    local c = ((b3 % 256) * 4 + math.floor(b2 / 256)) % 512
    local b = b4 * 2 + math.floor(b3 / 128)
    local i = {OP = op, A = a, B = b, C = c}
    if string.sub(self.opmodes[op + 1], 7, 7) ~= "C" then
        i.Bx = b * 512 + c
    end
    return i
end
function Instruction:ISK(x)
    return x >= self.BITRK
end
function Instruction:INDEXK(r)
    return r - self.BITRK
end
function Instruction:RKASK(x)
    return x + self.BITRK
end
function Instruction:getOpMode(m)
    return self.opmodes[self.OpCode[m]] % 4
end
function Instruction:getBMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 16) % 4
end
function Instruction:getCMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 4) % 4
end
function Instruction:testAMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 64) % 2
end
function Instruction:testTMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 128)
end
Instruction.LFIELDS_PER_FLUSH = 50
Serializer.LUA_SIGNATURE = "\27Lua"
Serializer.LUA_TNUMBER = 3
Serializer.LUA_TSTRING = 4
Serializer.LUA_TNIL = 0
Serializer.LUA_TBOOLEAN = 1
Serializer.LUA_TNONE = -1
Serializer.LUAC_VERSION = 81
Serializer.LUAC_FORMAT = 0
Serializer.LUAC_HEADERSIZE = 12
function Serializer:make_setS()
    local buff = {chunks = {}}
    local writer = function(s, buff)
        if not s then
            buff.data = table.concat(buff.chunks)
            return 0
        end
        table.insert(buff.chunks, s)
        return 0
    end
    return writer, buff
end
function Serializer:make_setF(filename)
    local buff = {}
    buff.h = io.open(filename, "wb")
    if not buff.h then
        return nil
    end
    local writer = function(s, buff)
        if not buff.h then
            return 0
        end
        if not s then
            if buff.h:close() then
                return 0
            end
        else
            if buff.h:write(s) then
                return 0
            end
        end
        return 1
    end
    return writer, buff
end
function Serializer:ttype(o)
    local tt = type(o.value)
    if tt == "number" then
        return self.LUA_TNUMBER
    elseif tt == "string" then
        return self.LUA_TSTRING
    elseif tt == "nil" then
        return self.LUA_TNIL
    elseif tt == "boolean" then
        return self.LUA_TBOOLEAN
    else
        return self.LUA_TNONE
    end
end
function frexp(x)
    if x == 0 then
        return 0, 0
    end
    local e = math.floor(math.log(math.abs(x)) / math.log(2)) + 1
    local m = x / 2 ^ e
    return m, e
end
function Serializer:from_double(x)
    local chunks = {}
    local function grab_byte(v)
        local c = v % 256
        return (v - c) / 256, string.char(c)
    end
    local sign = 0
    if x < 0 then
        sign = 1
        x = -x
    end
    local mantissa, exponent = frexp(x)
    if x == 0 then
        mantissa, exponent = 0, 0
    elseif x == 1 / 0 then
        mantissa, exponent = 0, 2047
    else
        mantissa = (mantissa * 2 - 1) * 2 ^ 52
        exponent = exponent + 1022
    end
    local v = math.floor(mantissa)
    for i = 1, 6 do
        v, chunks[i] = grab_byte(v)
    end
    v, chunks[7] = grab_byte(exponent * 16 + v)
    v, chunks[8] = grab_byte(sign * 128 + v)
    return table.concat(chunks)
end
function Serializer:from_int(x)
    local v = ""
    x = math.floor(x)
    if x < 0 then
        x = 4294967296 + x
    end
    for i = 1, 4 do
        local c = x % 256
        v = v .. string.char(c)
        x = math.floor(x / 256)
    end
    return v
end
function Serializer:DumpBlock(b, D)
    if D.status == 0 then
        D.status = D.write(b, D.data)
    end
end
function Serializer:DumpChar(y, D)
    self:DumpBlock(string.char(y), D)
end
function Serializer:DumpInt(x, D)
    self:DumpBlock(self:from_int(x), D)
end
function Serializer:DumpSizeT(x, D)
    self:DumpBlock(self:from_int(x), D)
    self:DumpBlock(self:from_int(0), D)
end
function Serializer:DumpNumber(x, D)
    self:DumpBlock(self:from_double(x), D)
end
function Serializer:DumpString(s, D)
    if s == nil then
        self:DumpSizeT(0, D)
    else
        self:DumpSizeT(#s + 1, D)
        self:DumpBlock(s .. "\0", D)
    end
end
function Serializer:DumpCode(f, D)
    local n = f.sizecode
    self:DumpInt(n, D)
    local chunks = {}
    for i = 0, n - 1 do
        chunks[i + 1] = Instruction:Instruction(f.code[i])
    end
    self:DumpBlock(table.concat(chunks), D)
end
function Serializer:DumpConstants(f, D)
    local n = f.sizek
    self:DumpInt(n, D)
    for i = 0, n - 1 do
        local o = f.k[i]
        local tt = self:ttype(o)
        self:DumpChar(tt, D)
        if tt == self.LUA_TNIL then
        elseif tt == self.LUA_TBOOLEAN then
            self:DumpChar(o.value and 1 or 0, D)
        elseif tt == self.LUA_TNUMBER then
            self:DumpNumber(o.value, D)
        elseif tt == self.LUA_TSTRING then
            self:DumpString(o.value, D)
        else
        end
    end
    n = f.sizep
    self:DumpInt(n, D)
    for i = 0, n - 1 do
        self:DumpFunction(f.p[i], f.source, D)
    end
end
function Serializer:DumpDebug(f, D)
    local n
    n = D.strip and 0 or f.sizelineinfo
    self:DumpInt(n, D)
    for i = 0, n - 1 do
        self:DumpInt(f.lineinfo[i], D)
    end
    n = D.strip and 0 or f.sizelocvars
    self:DumpInt(n, D)
    for i = 0, n - 1 do
        self:DumpString(f.locvars[i].varname, D)
        self:DumpInt(f.locvars[i].startpc, D)
        self:DumpInt(f.locvars[i].endpc, D)
    end
    n = D.strip and 0 or f.sizeupvalues
    self:DumpInt(n, D)
    for i = 0, n - 1 do
        self:DumpString(f.upvalues[i], D)
    end
end
function Serializer:DumpFunction(f, p, D)
    local source = f.source
    if source == p or D.strip then
        source = nil
    end
    self:DumpString(source, D)
    self:DumpInt(f.lineDefined, D)
    self:DumpInt(f.lastlinedefined, D)
    self:DumpChar(f.nups, D)
    self:DumpChar(f.numparams, D)
    self:DumpChar(f.is_vararg, D)
    self:DumpChar(f.maxstacksize, D)
    self:DumpCode(f, D)
    self:DumpConstants(f, D)
    self:DumpDebug(f, D)
end
function Serializer:DumpHeader(D)
    local h = self:header()
    assert(#h == self.LUAC_HEADERSIZE)
    self:DumpBlock(h, D)
end
function Serializer:header()
    local x = 1
    return self.LUA_SIGNATURE .. string.char(self.LUAC_VERSION, self.LUAC_FORMAT, x, 4, 8, 4, 8, 0)
end
function Serializer:dump(L, f, w, data, strip)
    local D = {}
    D.L = L
    D.write = w
    D.data = data
    D.strip = strip == nil and true or strip
    D.status = 0
    self:DumpHeader(D)
    self:DumpFunction(f, nil, D)
    D.write(nil, D.data)
    return D.status
end
Codegen.MAXSTACK = 250
function Codegen:ttisnumber(o)
    return o and type(o.value) == "number" or false
end
function Codegen:nvalue(o)
    return o.value
end
function Codegen:setnilvalue(o)
    o.value = nil
end
function Codegen:setsvalue(o, x)
    o.value = x
end
Codegen.setnvalue = Codegen.setsvalue
Codegen.sethvalue = Codegen.setsvalue
Codegen.setbvalue = Codegen.setsvalue
function Codegen:numadd(a, b)
    return a + b
end
function Codegen:numsub(a, b)
    return a - b
end
function Codegen:nummul(a, b)
    return a * b
end
function Codegen:numdiv(a, b)
    return a / b
end
function Codegen:nummod(a, b)
    return a % b
end
function Codegen:numpow(a, b)
    return a ^ b
end
function Codegen:numunm(a)
    return -a
end
function Codegen:numisnan(a)
    return a ~= a
end
Codegen.NO_JUMP = -1
Codegen.BinOpr = {
    OPR_ADD = 0,
    OPR_SUB = 1,
    OPR_MUL = 2,
    OPR_DIV = 3,
    OPR_MOD = 4,
    OPR_POW = 5,
    OPR_CONCAT = 6,
    OPR_NE = 7,
    OPR_EQ = 8,
    OPR_LT = 9,
    OPR_LE = 10,
    OPR_GT = 11,
    OPR_GE = 12,
    OPR_AND = 13,
    OPR_OR = 14,
    OPR_FLOORDIV = 15,
    OPR_FLOORDIV2 = 16,
    OPR_NOBINOPR = 17
}
Codegen.UnOpr = {OPR_MINUS = 0, OPR_NOT = 1, OPR_LEN = 2, OPR_NOUNOPR = 3}
function Codegen:getcode(fs, e)
    return fs.f.code[e.info]
end
function Codegen:codeAsBx(fs, o, A, sBx)
    return self:codeABx(fs, o, A, sBx + Instruction.MAXARG_sBx)
end
function Codegen:setmultret(fs, e)
    self:setreturns(fs, e, Parser.LUA_MULTRET)
end
function Codegen:hasjumps(e)
    return e.t ~= e.f
end
function Codegen:isnumeral(e)
    return e.k == "VKNUM" and e.t == self.NO_JUMP and e.f == self.NO_JUMP
end
function Codegen:_nil(fs, from, n)
    if fs.pc > fs.lasttarget then
        if fs.pc == 0 then
            if from >= fs.nactvar then
                return
            end
        else
            local previous = fs.f.code[fs.pc - 1]
            if Instruction:GET_OPCODE(previous) == "OP_LOADNIL" then
                local pfrom = Instruction:GETARG_A(previous)
                local pto = Instruction:GETARG_B(previous)
                if pfrom <= from and from <= pto + 1 then
                    if from + n - 1 > pto then
                        Instruction:SETARG_B(previous, from + n - 1)
                    end
                    return
                end
            end
        end
    end
    self:codeABC(fs, "OP_LOADNIL", from, from + n - 1, 0)
end
function Codegen:jump(fs)
    local jpc = fs.jpc
    fs.jpc = self.NO_JUMP
    local j = self:codeAsBx(fs, "OP_JMP", 0, self.NO_JUMP)
    j = self:concat(fs, j, jpc)
    return j
end
function Codegen:ret(fs, first, nret)
    self:codeABC(fs, "OP_RETURN", first, nret + 1, 0)
end
function Codegen:condjump(fs, op, A, B, C)
    self:codeABC(fs, op, A, B, C)
    return self:jump(fs)
end
function Codegen:fixjump(fs, pc, dest)
    local jmp = fs.f.code[pc]
    local offset = dest - (pc + 1)
    if math.abs(offset) > Instruction.MAXARG_sBx then
        Lexer:syntaxerror(fs.ls, "control structure too long")
    end
    Instruction:SETARG_sBx(jmp, offset)
end
function Codegen:getlabel(fs)
    fs.lasttarget = fs.pc
    return fs.pc
end
function Codegen:getjump(fs, pc)
    local offset = Instruction:GETARG_sBx(fs.f.code[pc])
    if offset == self.NO_JUMP then
        return self.NO_JUMP
    else
        return (pc + 1) + offset
    end
end
function Codegen:getjumpcontrol(fs, pc)
    local pi = fs.f.code[pc]
    local ppi = fs.f.code[pc - 1]
    if pc >= 1 and Instruction:testTMode(Instruction:GET_OPCODE(ppi)) ~= 0 then
        return ppi
    else
        return pi
    end
end
function Codegen:need_value(fs, list)
    while list ~= self.NO_JUMP do
        local i = self:getjumpcontrol(fs, list)
        if Instruction:GET_OPCODE(i) ~= "OP_TESTSET" then
            return true
        end
        list = self:getjump(fs, list)
    end
    return false
end
function Codegen:patchtestreg(fs, node, reg)
    local i = self:getjumpcontrol(fs, node)
    if Instruction:GET_OPCODE(i) ~= "OP_TESTSET" then
        return false
    end
    if reg ~= Instruction.NO_REG and reg ~= Instruction:GETARG_B(i) then
        Instruction:SETARG_A(i, reg)
    else
        Instruction:SET_OPCODE(i, "OP_TEST")
        local b = Instruction:GETARG_B(i)
        Instruction:SETARG_A(i, b)
        Instruction:SETARG_B(i, 0)
    end
    return true
end
function Codegen:removevalues(fs, list)
    while list ~= self.NO_JUMP do
        self:patchtestreg(fs, list, Instruction.NO_REG)
        list = self:getjump(fs, list)
    end
end
function Codegen:patchlistaux(fs, list, vtarget, reg, dtarget)
    while list ~= self.NO_JUMP do
        local _next = self:getjump(fs, list)
        if self:patchtestreg(fs, list, reg) then
            self:fixjump(fs, list, vtarget)
        else
            self:fixjump(fs, list, dtarget)
        end
        list = _next
    end
end
function Codegen:dischargejpc(fs)
    self:patchlistaux(fs, fs.jpc, fs.pc, Instruction.NO_REG, fs.pc)
    fs.jpc = self.NO_JUMP
end
function Codegen:patchlist(fs, list, target)
    if target == fs.pc then
        self:patchtohere(fs, list)
    else
        self:patchlistaux(fs, list, target, Instruction.NO_REG, target)
    end
end
function Codegen:patchtohere(fs, list)
    self:getlabel(fs)
    fs.jpc = self:concat(fs, fs.jpc, list)
end
function Codegen:concat(fs, l1, l2)
    if l2 == self.NO_JUMP then
        return l1
    elseif l1 == self.NO_JUMP then
        return l2
    else
        local list = l1
        local next = self:getjump(fs, list)
        while next ~= self.NO_JUMP do
            if next == l2 then
                return l1
            end
            list = next
            next = self:getjump(fs, list)
        end
        self:fixjump(fs, list, l2)
    end
    return l1
end
function Codegen:checkstack(fs, n)
    local newstack = fs.freereg + n
    if newstack > fs.f.maxstacksize then
        if newstack >= self.MAXSTACK then
            Lexer:syntaxerror(fs.ls, "function or expression too complex")
        end
        fs.f.maxstacksize = newstack
    end
end
function Codegen:reserveregs(fs, n)
    self:checkstack(fs, n)
    fs.freereg = fs.freereg + n
end
function Codegen:freereg(fs, reg)
    if not Instruction:ISK(reg) and reg >= fs.nactvar then
        fs.freereg = fs.freereg - 1
    end
end
function Codegen:freeexp(fs, e)
    if e.k == "VNONRELOC" then
        self:freereg(fs, e.info)
    end
end
function Codegen:addk(fs, k, v)
    local idx = fs.h[k.value]
    if self:ttisnumber(idx) then
        return self:nvalue(idx)
    end
    idx = {}
    self:setnvalue(idx, fs.nk)
    fs.h[k.value] = idx
    Parser:growvector(fs.L, fs.f.k, fs.nk, fs.f.sizek, nil, Instruction.MAXARG_Bx, "constant table overflow")
    fs.f.k[fs.nk] = v
    fs.nk = fs.nk + 1
    return fs.nk - 1
end
function Codegen:stringK(fs, s)
    local o = {}
    self:setsvalue(o, s)
    return self:addk(fs, o, o)
end
function Codegen:numberK(fs, r)
    local o = {}
    self:setnvalue(o, r)
    return self:addk(fs, o, o)
end
function Codegen:boolK(fs, b)
    local o = {}
    self:setbvalue(o, b)
    return self:addk(fs, o, o)
end
function Codegen:nilK(fs)
    local k, v = {}, {}
    self:setnilvalue(v)
    self:sethvalue(k, fs.h)
    return self:addk(fs, k, v)
end
function Codegen:setreturns(fs, e, nresults)
    if e.k == "VCALL" then
        Instruction:SETARG_C(self:getcode(fs, e), nresults + 1)
    elseif e.k == "VVARARG" then
        Instruction:SETARG_B(self:getcode(fs, e), nresults + 1)
        Instruction:SETARG_A(self:getcode(fs, e), fs.freereg)
        Codegen:reserveregs(fs, 1)
    end
end
function Codegen:setoneret(fs, e)
    if e.k == "VCALL" then
        e.k = "VNONRELOC"
        e.info = Instruction:GETARG_A(self:getcode(fs, e))
    elseif e.k == "VVARARG" then
        Instruction:SETARG_B(self:getcode(fs, e), 2)
        e.k = "VRELOCABLE"
    end
end
function Codegen:dischargevars(fs, e)
    local k = e.k
    if k == "VLOCAL" then
        e.k = "VNONRELOC"
    elseif k == "VUPVAL" then
        e.info = self:codeABC(fs, "OP_GETUPVAL", 0, e.info, 0)
        e.k = "VRELOCABLE"
    elseif k == "VGLOBAL" then
        e.info = self:codeABx(fs, "OP_GETGLOBAL", 0, e.info)
        e.k = "VRELOCABLE"
    elseif k == "VINDEXED" then
        self:freereg(fs, e.aux)
        self:freereg(fs, e.info)
        e.info = self:codeABC(fs, "OP_GETTABLE", 0, e.info, e.aux)
        e.k = "VRELOCABLE"
    elseif k == "VVARARG" or k == "VCALL" then
        self:setoneret(fs, e)
    else
    end
end
function Codegen:code_label(fs, A, b, jump)
    self:getlabel(fs)
    return self:codeABC(fs, "OP_LOADBOOL", A, b, jump)
end
function Codegen:discharge2reg(fs, e, reg)
    self:dischargevars(fs, e)
    local k = e.k
    if k == "VNIL" then
        self:_nil(fs, reg, 1)
    elseif k == "VFALSE" or k == "VTRUE" then
        self:codeABC(fs, "OP_LOADBOOL", reg, k == "VTRUE" and 1 or 0, 0)
    elseif k == "VK" then
        self:codeABx(fs, "OP_LOADK", reg, e.info)
    elseif k == "VKNUM" then
        self:codeABx(fs, "OP_LOADK", reg, self:numberK(fs, e.nval))
    elseif k == "VRELOCABLE" then
        local pc = fs.f.code[e.info]
        pc.A = reg
    elseif k == "VNONRELOC" then
        if reg ~= e.info then
            self:codeABC(fs, "OP_MOVE", reg, e.info, 0)
        end
    else
        return
    end
    e.info = reg
    e.k = "VNONRELOC"
end
function Codegen:discharge2anyreg(fs, e)
    if e.k ~= "VNONRELOC" then
        self:reserveregs(fs, 1)
        self:discharge2reg(fs, e, fs.freereg - 1)
    end
end
function Codegen:exp2reg(fs, e, reg)
    self:discharge2reg(fs, e, reg)
    if e.k == "VJMP" then
        e.t = self:concat(fs, e.t, e.info)
    end
    if self:hasjumps(e) then
        local final
        local p_f = self.NO_JUMP
        local p_t = self.NO_JUMP
        if self:need_value(fs, e.t) or self:need_value(fs, e.f) then
            local fj = (e.k == "VJMP") and self.NO_JUMP or self:jump(fs)
            p_f = self:code_label(fs, reg, 0, 1)
            p_t = self:code_label(fs, reg, 1, 0)
            self:patchtohere(fs, fj)
        end
        final = self:getlabel(fs)
        self:patchlistaux(fs, e.f, final, reg, p_f)
        self:patchlistaux(fs, e.t, final, reg, p_t)
    end
    e.f, e.t = self.NO_JUMP, self.NO_JUMP
    e.info = reg
    e.k = "VNONRELOC"
end
function Codegen:exp2nextreg(fs, e)
    self:dischargevars(fs, e)
    self:freeexp(fs, e)
    self:reserveregs(fs, 1)
    self:exp2reg(fs, e, fs.freereg - 1)
end
function Codegen:exp2anyreg(fs, e)
    self:dischargevars(fs, e)
    if e.k == "VNONRELOC" then
        if not self:hasjumps(e) then
            return e.info
        end
        if e.info >= fs.nactvar then
            self:exp2reg(fs, e, e.info)
            return e.info
        end
    end
    self:exp2nextreg(fs, e)
    return e.info
end
function Codegen:exp2val(fs, e)
    if self:hasjumps(e) then
        self:exp2anyreg(fs, e)
    else
        self:dischargevars(fs, e)
    end
end
function Codegen:exp2RK(fs, e)
    Codegen:exp2val(fs, e)
    local k = e.k
    if k == "VKNUM" or k == "VTRUE" or k == "VFALSE" or k == "VNIL" then
        if fs.nk <= Instruction.MAXINDEXRK then
            if k == "VNIL" then
                local o = {}
                Codegen:setnilvalue(o)
                local k_obj = {}
                Codegen:sethvalue(k_obj, fs.h)
                e.info = Codegen:addk(fs, k_obj, o)
            else
                e.info = (k == "VKNUM") and Codegen:numberK(fs, e.nval) or Codegen:boolK(fs, k == "VTRUE")
            end
            e.k = "VK"
            return Instruction:RKASK(e.info)
        end
    elseif k == "VK" and e.info <= Instruction.MAXINDEXRK then
        return Instruction:RKASK(e.info)
    end
    return Codegen:exp2anyreg(fs, e)
end
function Codegen:storevar(fs, var, ex)
    local k = var.k
    if k == "VLOCAL" then
        local locvar = Parser:getlocvar(fs, var.info)
        if locvar.is_const then
            Lexer:syntaxerror(fs.ls, "attempt to assign to const variable")
        end
        self:freeexp(fs, ex)
        self:exp2reg(fs, ex, var.info)
        return
    elseif k == "VUPVAL" then
        local e = self:exp2anyreg(fs, ex)
        self:codeABC(fs, "OP_SETUPVAL", e, var.info, 0)
    elseif k == "VGLOBAL" then
        local e = self:exp2anyreg(fs, ex)
        self:codeABx(fs, "OP_SETGLOBAL", e, var.info)
    elseif k == "VINDEXED" then
        local e = self:exp2RK(fs, ex)
        self:codeABC(fs, "OP_SETTABLE", var.info, var.aux, e)
    else
    end
    self:freeexp(fs, ex)
end
function Codegen:_self(fs, e, key)
    self:exp2anyreg(fs, e)
    self:freeexp(fs, e)
    local func = fs.freereg
    self:reserveregs(fs, 2)
    self:codeABC(fs, "OP_SELF", func, e.info, self:exp2RK(fs, key))
    self:freeexp(fs, key)
    e.info = func
    e.k = "VNONRELOC"
end
function Codegen:invertjump(fs, e)
    local pc = self:getjumpcontrol(fs, e.info)
    Instruction:SETARG_A(pc, (Instruction:GETARG_A(pc) == 0) and 1 or 0)
end
function Codegen:jumponcond(fs, e, cond)
    if e.k == "VRELOCABLE" then
        local ie = self:getcode(fs, e)
        if Instruction:GET_OPCODE(ie) == "OP_NOT" then
            fs.pc = fs.pc - 1
            return self:condjump(fs, "OP_TEST", Instruction:GETARG_B(ie), 0, cond and 0 or 1)
        end
    end
    self:discharge2anyreg(fs, e)
    self:freeexp(fs, e)
    return self:condjump(fs, "OP_TESTSET", Instruction.NO_REG, e.info, cond and 1 or 0)
end
function Codegen:goiftrue(fs, e)
    local pc
    self:dischargevars(fs, e)
    local k = e.k
    if k == "VK" or k == "VKNUM" or k == "VTRUE" then
        pc = self.NO_JUMP
    elseif k == "VFALSE" then
        pc = self:jump(fs)
    elseif k == "VJMP" then
        self:invertjump(fs, e)
        pc = e.info
    else
        pc = self:jumponcond(fs, e, false)
    end
    e.f = self:concat(fs, e.f, pc)
    self:patchtohere(fs, e.t)
    e.t = self.NO_JUMP
end
function Codegen:goiffalse(fs, e)
    local pc
    self:dischargevars(fs, e)
    local k = e.k
    if k == "VNIL" or k == "VFALSE" then
        pc = self.NO_JUMP
    elseif k == "VTRUE" then
        pc = self:jump(fs)
    elseif k == "VJMP" then
        pc = e.info
    else
        pc = self:jumponcond(fs, e, true)
    end
    e.t = self:concat(fs, e.t, pc)
    self:patchtohere(fs, e.f)
    e.f = self.NO_JUMP
end
function Codegen:codenot(fs, e)
    self:dischargevars(fs, e)
    local k = e.k
    if k == "VNIL" or k == "VFALSE" then
        e.k = "VTRUE"
    elseif k == "VK" or k == "VKNUM" or k == "VTRUE" then
        e.k = "VFALSE"
    elseif k == "VJMP" then
        self:invertjump(fs, e)
    elseif k == "VRELOCABLE" or k == "VNONRELOC" then
        self:discharge2anyreg(fs, e)
        self:freeexp(fs, e)
        e.info = self:codeABC(fs, "OP_NOT", 0, e.info, 0)
        e.k = "VRELOCABLE"
    else
    end
    e.f, e.t = e.t, e.f
    self:removevalues(fs, e.f)
    self:removevalues(fs, e.t)
end
function Codegen:indexed(fs, t, k)
    t.aux = self:exp2RK(fs, k)
    t.k = "VINDEXED"
end
function Codegen:code_floor(fs, src_reg, dest_reg)
    local math_idx = self:stringK(fs, "math")
    local floor_idx = self:stringK(fs, "floor")
    local func_reg = fs.freereg
    self:reserveregs(fs, 2)
    self:codeABx(fs, "OP_GETGLOBAL", func_reg, math_idx)
    self:codeABC(fs, "OP_GETTABLE", func_reg, func_reg, floor_idx + 256)
    self:codeABC(fs, "OP_MOVE", func_reg + 1, src_reg, 0)
    self:codeABC(fs, "OP_CALL", func_reg, 2, 2)
    self:codeABC(fs, "OP_MOVE", dest_reg, func_reg, 0)
    fs.freereg = func_reg
end
function Codegen:constfolding(op, e1, e2)
    local v1, v2
    if e1.k == "VKNUM" then
        v1 = e1.nval
    end
    if op == "OP_UNM" then
        v2 = 0
    elseif e2.k == "VKNUM" then
        v2 = e2.nval
    end
    if op == "OP_CONCAT" and e1.k == "VK" and e2.k == "VK" then
        e1.nval, e1.k = fs.f.k[e1.info].value .. fs.f.k[e2.info].value, "VK"
        return true
    elseif op == "OPR_AND" and e1.k == "VFALSE" or op == "OPR_OR" and e1.k == "VTRUE" then
        return true
    elseif not v1 or (op ~= "OP_UNM" and not v2) then
        return false
    end
    local r
    if op == "OP_ADD" then
        r = self:numadd(v1, v2)
    elseif op == "OP_SUB" then
        r = self:numsub(v1, v2)
    elseif op == "OP_MUL" then
        r = self:nummul(v1, v2)
    elseif op == "OP_DIV" and v2 ~= 0 then
        r = self:numdiv(v1, v2)
    elseif op == "OP_MOD" and v2 ~= 0 then
        r = self:nummod(v1, v2)
    elseif op == "OP_POW" then
        r = self:numpow(v1, v2)
    elseif op == "OP_UNM" then
        r = self:numunm(v1)
    elseif op == "OP_FLOORDIV" and v2 ~= 0 then
        r = math.floor(self:numdiv(v1, v2))
    else
        return false
    end
    if self:numisnan(r) then
        return false
    end
    e1.nval, e1.k = r, "VKNUM"
    return true
end
function Codegen:codearith(fs, op, e1, e2)
    if self:constfolding(op, e1, e2) then
        return
    else
        if op == "OP_FLOORDIV" then
            local o1 = self:exp2anyreg(fs, e1)
            local o2 = self:exp2anyreg(fs, e2)
            self:freeexp(fs, e1)
            self:freeexp(fs, e2)
            local div_reg = fs.freereg
            self:reserveregs(fs, 1)
            self:codeABC(fs, "OP_DIV", div_reg, o1, o2)
            self:code_floor(fs, div_reg, div_reg)
            e1.k = "VNONRELOC"
            e1.info = div_reg
        else
            local o2 = (op ~= "OP_UNM" and op ~= "OP_LEN") and self:exp2RK(fs, e2) or 0
            local o1 = self:exp2RK(fs, e1)
            if o1 > o2 then
                self:freeexp(fs, e1)
                self:freeexp(fs, e2)
            else
                self:freeexp(fs, e2)
                self:freeexp(fs, e1)
            end
            e1.info = self:codeABC(fs, op, 0, o1, o2)
            e1.k = "VRELOCABLE"
        end
    end
end
function Codegen:codecomp(fs, op, cond, e1, e2)
    local o1 = self:exp2RK(fs, e1)
    local o2 = self:exp2RK(fs, e2)
    self:freeexp(fs, e2)
    self:freeexp(fs, e1)
    if cond == 0 and op ~= "OP_EQ" then
        o1, o2 = o2, o1
        cond = 1
    end
    e1.info = self:condjump(fs, op, cond, o1, o2)
    e1.k = "VJMP"
end
function Codegen:prefix(fs, op, e)
    local e2 = {}
    e2.t, e2.f = self.NO_JUMP, self.NO_JUMP
    e2.k = "VKNUM"
    e2.nval = 0
    if op == "OPR_MINUS" then
        if not self:isnumeral(e) then
            self:exp2anyreg(fs, e)
        end
        self:codearith(fs, "OP_UNM", e, e2)
    elseif op == "OPR_NOT" then
        self:codenot(fs, e)
    elseif op == "OPR_LEN" then
        self:exp2anyreg(fs, e)
        self:codearith(fs, "OP_LEN", e, e2)
    else
    end
end
function Codegen:infix(fs, op, v)
    if op == "OPR_AND" then
        self:goiftrue(fs, v)
    elseif op == "OPR_OR" then
        self:goiffalse(fs, v)
    elseif op == "OPR_CONCAT" then
        self:exp2nextreg(fs, v)
    elseif
        op == "OPR_ADD" or op == "OPR_SUB" or op == "OPR_MUL" or op == "OPR_DIV" or op == "OPR_MOD" or op == "OPR_POW"
     then
        if not self:isnumeral(v) then
            self:exp2RK(fs, v)
        end
    else
        self:exp2RK(fs, v)
    end
end
Codegen.arith_op = {
    OPR_ADD = "OP_ADD",
    OPR_SUB = "OP_SUB",
    OPR_MUL = "OP_MUL",
    OPR_DIV = "OP_DIV",
    OPR_MOD = "OP_MOD",
    OPR_POW = "OP_POW",
    OPR_FLOORDIV = "OP_FLOORDIV"
}
Codegen.comp_op = {
    OPR_EQ = "OP_EQ",
    OPR_NE = "OP_EQ",
    OPR_LT = "OP_LT",
    OPR_LE = "OP_LE",
    OPR_GT = "OP_LT",
    OPR_GE = "OP_LE"
}
Codegen.comp_cond = {OPR_EQ = 1, OPR_NE = 0, OPR_LT = 1, OPR_LE = 1, OPR_GT = 0, OPR_GE = 0}
function Codegen:posfix(fs, op, e1, e2)
    local function copyexp(e1, e2)
        e1.k = e2.k
        e1.info = e2.info
        e1.aux = e2.aux
        e1.nval = e2.nval
        e1.t = e2.t
        e1.f = e2.f
    end
    if op == "OPR_AND" then
        self:dischargevars(fs, e2)
        e2.f = self:concat(fs, e2.f, e1.f)
        copyexp(e1, e2)
    elseif op == "OPR_OR" then
        self:dischargevars(fs, e2)
        e2.t = self:concat(fs, e2.t, e1.t)
        copyexp(e1, e2)
    elseif op == "OPR_CONCAT" or op == "OPR_CONCAT2" then
        self:exp2val(fs, e2)
        if e2.k == "VRELOCABLE" and Instruction:GET_OPCODE(self:getcode(fs, e2)) == "OP_CONCAT" then
            self:freeexp(fs, e1)
            Instruction:SETARG_B(self:getcode(fs, e2), e1.info)
            e1.k = "VRELOCABLE"
            e1.info = e2.info
        else
            self:exp2nextreg(fs, e2)
            self:codearith(fs, "OP_CONCAT", e1, e2)
        end
    else
        local arith = self.arith_op[op]
        if arith then
            self:codearith(fs, arith, e1, e2)
        else
            local comp = self.comp_op[op]
            if comp then
                self:codecomp(fs, comp, self.comp_cond[op], e1, e2)
            else
                Lexer:syntaxerror(fs.ls, string.format("unsupported binary operator '%s'", op))
            end
        end
    end
end
function Codegen:fixline(fs, line)
    fs.f.lineinfo[fs.pc - 1] = line
end
function Codegen:code(fs, i, line)
    local f = fs.f
    self:dischargejpc(fs)
    Parser:growvector(fs.L, f.code, fs.pc, f.sizecode, nil, Parser.MAX_INT, "code size overflow")
    f.code[fs.pc] = i
    Parser:growvector(fs.L, f.lineinfo, fs.pc, f.sizelineinfo, nil, Parser.MAX_INT, "code size overflow")
    f.lineinfo[fs.pc] = line
    local pc = fs.pc
    fs.pc = fs.pc + 1
    return pc
end
function Codegen:codeABC(fs, o, a, b, c)
    local i = {OP = Instruction.OpCode[o], A = a, B = b, C = c}
    local f = fs.f
    Codegen:dischargejpc(fs)
    Parser:growvector(fs.L, f.code, fs.pc, f.sizecode, nil, Parser.MAX_INT, "code size overflow")
    f.code[fs.pc] = i
    Parser:growvector(fs.L, f.lineinfo, fs.pc, f.sizelineinfo, nil, Parser.MAX_INT, "code size overflow")
    f.lineinfo[fs.pc] = fs.ls.lastline
    local pc = fs.pc
    fs.pc = fs.pc + 1
    return pc
end
function Codegen:codeABx(fs, o, a, bc)
    return self:code(fs, Instruction:CREATE_ABx(o, a, bc), fs.ls.lastline)
end
function Codegen:setlist(fs, base, nelems, tostore)
    local c = math.floor((nelems - 1) / Instruction.LFIELDS_PER_FLUSH) + 1
    local b = (tostore == Parser.LUA_MULTRET) and 0 or tostore
    if c <= Instruction.MAXARG_C then
        self:codeABC(fs, "OP_SETLIST", base, b, c)
    else
        self:codeABC(fs, "OP_SETLIST", base, b, 0)
        self:code(fs, Instruction:CREATE_Inst(c), fs.ls.lastline)
    end
    fs.freereg = base + 1
end
Parser.SHRT_MAX = 32767
Parser.LUAI_MAXVARS = 200
Parser.LUAI_MAXUPVALUES = 60
Parser.MAX_INT = Lexer.MAX_INT or 2147483645
Parser.LUAI_MAXCCALLS = 200
Parser.VARARG_HASARG = 1
Parser.HASARG_MASK = 2
Parser.VARARG_ISVARARG = 2
Parser.VARARG_NEEDSARG = 4
Parser.LUA_MULTRET = -1
function Parser:LUA_QL(x)
    return "'" .. x .. "'"
end
function Parser:growvector(L, v, nelems, size, t, limit, e)
    if nelems >= limit then
        error(e)
    end
end
function Parser:newproto(L)
    local f = {}
    f.k = {}
    f.sizek = 0
    f.p = {}
    f.sizep = 0
    f.code = {}
    f.sizecode = 0
    f.sizelineinfo = 0
    f.sizeupvalues = 0
    f.nups = 0
    f.upvalues = {}
    f.numparams = 0
    f.is_vararg = 0
    f.maxstacksize = 0
    f.lineinfo = {}
    f.sizelocvars = 0
    f.locvars = {}
    f.lineDefined = 0
    f.lastlinedefined = 0
    f.source = nil
    return f
end
function Parser:int2fb(x)
    local e = 0
    while x >= 16 do
        x = math.floor((x + 1) / 2)
        e = e + 1
    end
    if x < 8 then
        return x
    else
        return ((e + 1) * 8) + (x - 8)
    end
end
function Parser:hasmultret(k)
    return k == "VCALL" or k == "VVARARG"
end
function Parser:getlocvar(fs, i)
    return fs.f.locvars[fs.actvar[i]]
end
function Parser:checklimit(fs, v, l, m)
    if v > l then
        self:errorlimit(fs, l, m)
    end
end
function Parser:anchor_token(ls)
    if ls.t.token == "TK_NAME" or ls.t.token == "TK_STRING" then
    end
end
function Parser:error_expected(ls, token)
    Lexer:syntaxerror(ls, string.format("'%s' expected", Lexer:token2str(ls, token)))
end
function Parser:errorlimit(fs, limit, what)
    local msg =
        (fs.f.linedefined == 0) and string.format("main function has more than %d %s", limit, what) or
        string.format("function at line %d has more than %d %s", fs.f.linedefined, limit, what)
    Lexer:lexererror(fs.ls, msg, 0)
end
function Parser:testnext(ls, c)
    if ls.t.token == c then
        Lexer:next(ls)
        return true
    else
        return false
    end
end
function Parser:check(ls, c)
    if ls.t.token ~= c then
        self:error_expected(ls, c)
    end
end
function Parser:checknext(ls, c)
    self:check(ls, c)
    Lexer:next(ls)
end
function Parser:check_condition(ls, c, msg)
    if not c then
        Lexer:syntaxerror(ls, msg)
    end
end
function Parser:check_match(ls, what, who, where)
    if not self:testnext(ls, what) then
        Lexer:syntaxerror(
            ls,
            where == ls.linenumber and self.LUA_QS:format(Lexer:token2str(ls, what)) .. " expected" or
                self.LUA_QS:format(Lexer:token2str(ls, what)) ..
                    " expected (to close " .. self.LUA_QS:format(Lexer:token2str(ls, who)) .. " at line %d)",
            where
        )
    end
end
function Parser:str_checkname(ls)
    self:check(ls, "TK_NAME")
    local ts = ls.t.seminfo
    Lexer:next(ls)
    return ts
end
function Parser:init_exp(e, k, i)
    e.f, e.t = Codegen.NO_JUMP, Codegen.NO_JUMP
    e.k = k
    e.info = i
    e.nval = nil
    e.aux = nil
    return e
end
function Parser:codestring(ls, e, s)
    e.f, e.t = Codegen.NO_JUMP, Codegen.NO_JUMP
    e.k = "VK"
    e.info = Codegen:stringK(ls.fs, s)
    e.nval = nil
    e.aux = nil
end
local function is_valid_type(type_name)
    return true
end
local function emit_type_check(fs, reg, expected_type, line)
end
function Parser:checkname(ls, e, allow_type)
    local token = ls.t.token
    local name
    if token == "TK_NAME" then
        name = ls.t.seminfo
        Lexer:next(ls)
    elseif token == "TK_CONTINUE" or token == "TK_VAL" or token == "TK_GOTO" then
        name = Lexer.tokens[token]
        Lexer:next(ls)
    else
        self:error_expected(ls, "TK_NAME")
    end
    local type_annot = nil
    if allow_type and ls.t.token == ":" then
        Lexer:next(ls)
        self:check(ls, "TK_NAME")
        type_annot = ls.t.seminfo
        if not is_valid_type(type_annot) then
            Lexer:syntaxerror(ls, string.format("Invalid type annotation '%s'", type_annot))
        end
        Lexer:next(ls)
    end
    self:codestring(ls, e, name)
    return name, type_annot
end
function Parser:registerlocalvar(ls, varname, is_const, is_close)
    local fs = ls.fs
    local f = fs.f
    self:growvector(ls.L, f.locvars, fs.nlocvars, f.sizelocvars, nil, self.SHRT_MAX, "too many local variables")
    f.locvars[fs.nlocvars] = {varname = varname, is_const = is_const or false, is_close = is_close or false}
    local nlocvars = fs.nlocvars
    fs.nlocvars = fs.nlocvars + 1
    return nlocvars
end
function Parser:new_localvarliteral(ls, v, n)
    self:new_localvar(ls, v, n)
end
function Parser:new_localvar(ls, name, n, is_const, is_close)
    local fs = ls.fs
    self:checklimit(fs, fs.nactvar + n + 1, self.LUAI_MAXVARS, "local variables")
    fs.actvar[fs.nactvar + n] = self:registerlocalvar(ls, name, is_const, is_close)
end
function Parser:adjustlocalvars(ls, nvars)
    local fs = ls.fs
    fs.nactvar = fs.nactvar + nvars
    for i = nvars, 1, -1 do
        self:getlocvar(fs, fs.nactvar - i).startpc = fs.pc
    end
end
function Parser:removevars(ls, tolevel)
    local fs = ls.fs
    while fs.nactvar > tolevel do
        fs.nactvar = fs.nactvar - 1
        local locvar = self:getlocvar(fs, fs.nactvar)
        locvar.endpc = fs.pc
    end
end
function Parser:indexupvalue(fs, name, v)
    local f = fs.f
    for i = 0, f.nups - 1 do
        if fs.upvalues[i].k == v.k and fs.upvalues[i].info == v.info then
            return i
        end
    end
    self:checklimit(fs, f.nups + 1, self.LUAI_MAXUPVALUES, "upvalues")
    self:growvector(fs.L, f.upvalues, f.nups, f.sizeupvalues, nil, self.MAX_INT, "")
    f.upvalues[f.nups] = name
    fs.upvalues[f.nups] = {k = v.k, info = v.info}
    local nups = f.nups
    f.nups = f.nups + 1
    return nups
end
function Parser:searchvar(fs, n)
    for i = fs.nactvar - 1, 0, -1 do
        if n == self:getlocvar(fs, i).varname then
            return i
        end
    end
    return -1
end
function Parser:markupval(fs, level)
    local bl = fs.bl
    while bl and bl.nactvar > level do
        bl = bl.previous
    end
    if bl then
        bl.upval = true
    end
end
function Parser:singlevaraux(fs, n, var, base)
    if fs == nil then
        self:init_exp(var, "VGLOBAL", Instruction.NO_REG)
        return "VGLOBAL"
    else
        local v = self:searchvar(fs, n)
        if v >= 0 then
            self:init_exp(var, "VLOCAL", v)
            if base == 0 then
                self:markupval(fs, v)
            end
            return "VLOCAL"
        else
            if self:singlevaraux(fs.prev, n, var, 0) == "VGLOBAL" then
                return "VGLOBAL"
            end
            var.info = self:indexupvalue(fs, n, var)
            var.k = "VUPVAL"
            return "VUPVAL"
        end
    end
end
function Parser:singlevar(ls, var)
    local varname = self:str_checkname(ls)
    local fs = ls.fs
    if self:singlevaraux(fs, varname, var, 1) == "VGLOBAL" then
        var.info = Codegen:stringK(fs, varname)
    end
end
function Parser:adjust_assign(ls, nvars, nexps, e)
    local fs, extra = ls.fs, nvars - nexps
    if self:hasmultret(e.k) then
        extra = extra + 1
        Codegen:setreturns(fs, e, extra < 0 and 0 or extra)
        if extra > 1 then
            Codegen:reserveregs(fs, extra - 1)
        end
    else
        if e.k ~= "VVOID" then
            Codegen:exp2nextreg(fs, e)
        end
        if extra > 0 then
            Codegen:_nil(fs, fs.freereg, extra)
            Codegen:reserveregs(fs, extra)
        elseif nexps == 1 and nvars > 1 then
            local reg = fs.freereg - 1
            Codegen:reserveregs(fs, nvars - 1)
            for i = 1, nvars - 1 do
                Codegen:codeABC(fs, "OP_MOVE", reg + i, reg, 0)
            end
        end
    end
end
function Parser:enterlevel(ls)
    ls.L.nCcalls = ls.L.nCcalls + 1
    if ls.L.nCcalls > self.LUAI_MAXCCALLS then
        Lexer:lexererror(ls, "chunk has too many syntax levels", 0)
    end
end
function Parser:leavelevel(ls)
    ls.L.nCcalls = ls.L.nCcalls - 1
end
function Parser:enterblock(fs, bl, isbreakable)
    bl.breaklist = Codegen.NO_JUMP
    bl.continuelist = Codegen.NO_JUMP
    bl.isbreakable = isbreakable
    bl.nactvar = fs.nactvar
    bl.upval = false
    bl.previous = fs.bl
    fs.bl = bl
end
function Parser:leaveblock(fs)
    local bl = fs.bl
    fs.bl = bl.previous
    self:removevars(fs.ls, bl.nactvar)
    if bl.upval then
        Codegen:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
    end
    fs.freereg = fs.nactvar
    Codegen:patchtohere(fs, bl.breaklist)
end
function Parser:pushclosure(ls, func, v)
    local fs = ls.fs
    local f = fs.f
    self:growvector(ls.L, f.p, fs.np, f.sizep, nil, Instruction.MAXARG_Bx, "constant table overflow")
    f.p[fs.np] = func.f
    fs.np = fs.np + 1
    self:init_exp(v, "VRELOCABLE", Codegen:codeABx(fs, "OP_CLOSURE", 0, fs.np - 1))
    for i = 0, func.f.nups - 1 do
        local o = (func.upvalues[i].k == "VLOCAL") and "OP_MOVE" or "OP_GETUPVAL"
        Codegen:codeABC(fs, o, 0, func.upvalues[i].info, 0)
    end
end
function Parser:open_func(ls, fs)
    local L = ls.L
    local f = self:newproto(ls.L)
    fs.f = f
    fs.prev = ls.fs
    fs.ls = ls
    fs.L = L
    ls.fs = fs
    fs.pc = 0
    fs.lasttarget = -1
    fs.jpc = Codegen.NO_JUMP
    fs.freereg = 0
    fs.nk = 0
    fs.np = 0
    fs.nlocvars = 0
    fs.nactvar = 0
    fs.bl = nil
    fs.labels = {}
    fs.sizelabels = 0
    fs.nlabels = 0
    fs.pendinggotos = {}
    fs.sizependinggotos = 0
    fs.npendinggotos = 0
    f.source = ls.source
    f.maxstacksize = 2
    fs.h = {}
end
function Parser:close_func(ls)
    local fs = ls.fs
    local f = fs.f
    self:removevars(ls, 0)
    Codegen:ret(fs, 0, 0)
    for i = 0, fs.npendinggotos - 1 do
        local g = fs.pendinggotos[i]
        local target = self:searchlabel(fs, g.label)
        if target < 0 then
            Lexer:syntaxerror(ls, string.format("label '%s' not found", g.label))
        end
        local label_nactvar = -1
        for j = 0, fs.nlabels - 1 do
            local lbl = fs.labels[j]
            if lbl.name == g.label then
                label_nactvar = lbl.nactvar
                break
            end
        end
        if label_nactvar > g.nactvar then
            Lexer:syntaxerror(ls, "goto skips local variable declaration")
        end
        Codegen:fixjump(fs, g.pc, target)
    end
    f.sizecode = fs.pc
    f.sizelineinfo = fs.pc
    f.sizek = fs.nk
    f.sizep = fs.np
    f.sizelocvars = fs.nlocvars
    f.sizeupvalues = f.nups
    ls.fs = fs.prev
end
function Parser:parser(L, z, buff, name)
    local lexstate = {t = {}, lookahead = {}}
    local funcstate = {upvalues = {}, actvar = {}}
    L.nCcalls = 0
    lexstate.buff = buff
    Lexer:setinput(L, lexstate, z, name)
    Parser:open_func(lexstate, funcstate)
    funcstate.f.is_vararg = Parser.VARARG_ISVARARG
    Lexer:next(lexstate)
    Parser:chunk(lexstate)
    Parser:checknext(lexstate, "TK_EOS")
    Parser:close_func(lexstate)
    return funcstate.f
end
function Parser:field(ls, v)
    local fs = ls.fs
    local key = {}
    Codegen:exp2anyreg(fs, v)
    Lexer:next(ls)
    local token = ls.t.token
    if token == "TK_NAME" then
        key.seminfo = ls.t.seminfo
        Lexer:next(ls)
    elseif Lexer.tokens[token] and type(Lexer.tokens[token]) == "string" then
        key.seminfo = Lexer.tokens[token]
        Lexer:next(ls)
    else
        Lexer:syntaxerror(ls, "field name expected")
    end
    self:codestring(ls, key, key.seminfo)
    Codegen:indexed(fs, v, key)
end
function Parser:yindex(ls, v)
    Lexer:next(ls)
    self:expr(ls, v)
    Codegen:exp2val(ls.fs, v)
    self:checknext(ls, "]")
end
function Parser:recfield(ls, cc)
    local fs = ls.fs
    local reg = ls.fs.freereg
    local key, val = {}, {}
    local type_annot = nil
    if ls.t.token == "TK_NAME" or (Lexer.tokens[ls.t.token] and type(Lexer.tokens[ls.t.token]) == "string") then
        self:checklimit(fs, cc.nh, self.MAX_INT, "items in a constructor")
        local name
        if ls.t.token == "TK_NAME" then
            name = ls.t.seminfo
            Lexer:next(ls)
        else
            name = Lexer.tokens[ls.t.token]
            Lexer:next(ls)
        end
        if ls.t.token == ":" then
            Lexer:next(ls)
            self:check(ls, "TK_NAME")
            type_annot = ls.t.seminfo
            if not is_valid_type(type_annot) then
                Lexer:syntaxerror(ls, string.format("Invalid type annotation '%s'", type_annot))
            end
            Lexer:next(ls)
        end
        self:codestring(ls, key, name)
    else
        self:yindex(ls, key)
    end
    cc.nh = cc.nh + 1
    self:checknext(ls, "=")
    local rkkey = Codegen:exp2RK(fs, key)
    self:expr(ls, val)
    if type_annot then
        local val_reg = Codegen:exp2anyreg(fs, val)
        emit_type_check(fs, val_reg, type_annot, ls.linenumber)
    end
    Codegen:codeABC(fs, "OP_SETTABLE", cc.t.info, rkkey, Codegen:exp2RK(fs, val))
    fs.freereg = reg
end
function Parser:closelistfield(fs, cc)
    if cc.v.k == "VVOID" then
        return
    end
    Codegen:exp2nextreg(fs, cc.v)
    cc.v.k = "VVOID"
    if cc.tostore == Instruction.LFIELDS_PER_FLUSH then
        Codegen:setlist(fs, cc.t.info, cc.na, cc.tostore)
        cc.tostore = 0
    end
end
function Parser:lastlistfield(fs, cc)
    if cc.tostore == 0 then
        return
    end
    if self:hasmultret(cc.v.k) then
        Codegen:setmultret(fs, cc.v)
        Codegen:setlist(fs, cc.t.info, cc.na, self.LUA_MULTRET)
        cc.na = cc.na - 1
    else
        if cc.v.k ~= "VVOID" then
            Codegen:exp2nextreg(fs, cc.v)
        end
        Codegen:setlist(fs, cc.t.info, cc.na, cc.tostore)
    end
end
function Parser:listfield(ls, cc)
    self:expr(ls, cc.v)
    self:checklimit(ls.fs, cc.na, self.MAX_INT, "items in a constructor")
    cc.na = cc.na + 1
    cc.tostore = cc.tostore + 1
end
function Parser:constructor(ls, t)
    local fs = ls.fs
    local line = ls.linenumber
    local pc = Codegen:codeABC(fs, "OP_NEWTABLE", 0, 0, 0)
    local cc = {}
    cc.v = {}
    cc.na, cc.nh, cc.tostore = 0, 0, 0
    cc.t = t
    self:init_exp(t, "VRELOCABLE", pc)
    self:init_exp(cc.v, "VVOID", 0)
    Codegen:exp2nextreg(ls.fs, t)
    self:checknext(ls, "{")
    repeat
        if ls.t.token == "}" then
            break
        end
        self:closelistfield(fs, cc)
        local c = ls.t.token
        if c == "TK_NAME" then
            Lexer:lookahead(ls)
            if ls.lookahead.token ~= "=" then
                self:listfield(ls, cc)
            else
                self:recfield(ls, cc)
            end
        elseif c == "[" then
            self:recfield(ls, cc)
        else
            self:listfield(ls, cc)
        end
    until not self:testnext(ls, ",") and not self:testnext(ls, ";")
    self:check_match(ls, "}", "{", line)
    self:lastlistfield(fs, cc)
    Instruction:SETARG_B(fs.f.code[pc], self:int2fb(cc.na))
    Instruction:SETARG_C(fs.f.code[pc], self:int2fb(cc.nh))
end
function Parser:parlist(ls)
    local fs = ls.fs
    local f = fs.f
    local nparams = 0
    local param_types = {}
    f.is_vararg = 0
    if ls.t.token ~= ")" then
        repeat
            local c = ls.t.token
            if c == "TK_NAME" then
                local name, type_annot = self:checkname(ls, {}, true)
                self:new_localvar(ls, name, nparams)
                param_types[nparams + 1] = type_annot
                if type_annot then
                    emit_type_check(fs, nparams, type_annot, ls.linenumber)
                end
                nparams = nparams + 1
            elseif c == "TK_DOTS" then
                Lexer:next(ls)
                self:new_localvarliteral(ls, "arg", nparams)
                nparams = nparams + 1
                f.is_vararg = self.VARARG_HASARG + self.VARARG_NEEDSARG
                f.is_vararg = f.is_vararg + self.VARARG_ISVARARG
            else
                Lexer:syntaxerror(ls, "<name> or " .. self:LUA_QL("...") .. " expected")
            end
        until f.is_vararg ~= 0 or not self:testnext(ls, ",")
    end
    self:adjustlocalvars(ls, nparams)
    f.numparams = fs.nactvar - (f.is_vararg % self.HASARG_MASK)
    Codegen:reserveregs(fs, fs.nactvar)
    return param_types
end
function Parser:body(ls, e, needself, line)
    local new_fs = {}
    new_fs.upvalues = {}
    new_fs.actvar = {}
    self:open_func(ls, new_fs)
    new_fs.f.lineDefined = line
    self:checknext(ls, "(")
    if needself then
        self:new_localvarliteral(ls, "self", 0)
        self:adjustlocalvars(ls, 1)
    end
    local param_types = self:parlist(ls)
    self:checknext(ls, ")")
    if ls.t.token == ":" then
        Lexer:next(ls)
        self:check(ls, "TK_NAME")
        local return_type = ls.t.seminfo
        if not is_valid_type(return_type) then
            Lexer:syntaxerror(ls, string.format("Invalid return type '%s'", return_type))
        end
        Lexer:next(ls)
        e.return_type = return_type
    end
    self:chunk(ls)
    new_fs.f.lastlinedefined = ls.linenumber
    self:check_match(ls, "TK_END", "TK_FUNCTION", line)
    if e.return_type and e.return_type ~= "()" then
        local ret_reg = new_fs.freereg
        Codegen:reserveregs(new_fs, 1)
        Codegen:codeABC(new_fs, "OP_RETURN", ret_reg, 2, 0)
        emit_type_check(new_fs, ret_reg, e.return_type, ls.linenumber)
    end
    self:close_func(ls)
    self:pushclosure(ls, new_fs, e)
end
function Parser:explist1(ls, v)
    local n = 1
    self:expr(ls, v)
    while self:testnext(ls, ",") do
        Codegen:exp2nextreg(ls.fs, v)
        self:expr(ls, v)
        n = n + 1
    end
    return n
end
function Parser:funcargs(ls, f)
    local fs = ls.fs
    local args = {}
    local nparams
    local line = ls.linenumber
    local c = ls.t.token
    if c == "(" then
        if line ~= ls.lastline then
            Lexer:syntaxerror(ls, "ambiguous syntax (function call x new statement)")
        end
        Lexer:next(ls)
        if ls.t.token == ")" then
            args.k = "VVOID"
        else
            self:explist1(ls, args)
            Codegen:setmultret(fs, args)
        end
        self:check_match(ls, ")", "(", line)
    elseif c == "{" then
        self:constructor(ls, args)
    elseif c == "TK_STRING" then
        self:codestring(ls, args, ls.t.seminfo)
        Lexer:next(ls)
    else
        Lexer:syntaxerror(ls, "function arguments expected")
        return
    end
    local base = f.info
    if self:hasmultret(args.k) then
        nparams = self.LUA_MULTRET
    else
        if args.k ~= "VVOID" then
            Codegen:exp2nextreg(fs, args)
        end
        nparams = fs.freereg - (base + 1)
    end
    self:init_exp(f, "VCALL", Codegen:codeABC(fs, "OP_CALL", base, nparams + 1, 2))
    Codegen:fixline(fs, line)
    fs.freereg = base + 1
end
function Parser:prefixexp(ls, v)
    local c = ls.t.token
    if c == "(" then
        local line = ls.linenumber
        Lexer:next(ls)
        self:expr(ls, v)
        self:check_match(ls, ")", "(", line)
        Codegen:dischargevars(ls.fs, v)
    elseif c == "TK_NAME" then
        self:singlevar(ls, v)
    else
        Lexer:syntaxerror(ls, "unexpected symbol")
    end
    return
end
function Parser:primaryexp(ls, v)
    local fs = ls.fs
    local c = ls.t.token
    local line = ls.linenumber
    if c == "(" then
        Lexer:next(ls)
        self:expr(ls, v)
        self:check_match(ls, ")", "(", line)
        Codegen:dischargevars(fs, v)
    elseif c == "TK_NAME" then
        self:singlevar(ls, v)
    else
        Lexer:syntaxerror(ls, string.format("unexpected symbol '%s'", Lexer:token2str(ls, c)))
    end
    while true do
        c = ls.t.token
        if c == "." then
            self:field(ls, v)
        elseif c == "[" then
            local key = {}
            Codegen:exp2anyreg(fs, v)
            self:yindex(ls, key)
            Codegen:indexed(fs, v, key)
        elseif c == ":" then
            local key = {}
            Lexer:next(ls)
            self:checkname(ls, key)
            Codegen:_self(fs, v, key)
            self:funcargs(ls, v)
        elseif c == "TK_DOUBLECOLON" then
            Lexer:next(ls)
            self:check(ls, "TK_NAME")
            local type_assert = ls.t.seminfo
            if not is_valid_type(type_assert) then
                Lexer:syntaxerror(ls, string.format("Invalid type assertion '%s'", type_assert))
            end
            Lexer:next(ls)
            local reg = Codegen:exp2anyreg(fs, v)
            emit_type_check(fs, reg, type_assert, ls.linenumber)
            v.k = "VNONRELOC"
            v.info = reg
        elseif c == "(" or c == "TK_STRING" or c == "{" then
            Codegen:exp2nextreg(fs, v)
            self:funcargs(ls, v)
        else
            return
        end
    end
end
function Parser:gotostat(ls)
    local fs = ls.fs
    local label = self:getlabelname(ls)
    self:addpendinggoto(fs, label, Codegen:jump(fs))
    fs.pendinggotos[fs.npendinggotos - 1].nactvar = fs.nactvar
end
function Parser:labelstat(ls, line)
    local label = self:getlabelname(ls)
    local fs = ls.fs
    self:checkrepeated(fs, label)
    local g = Codegen:getlabel(fs)
    self:addlabel(fs, label, g)
    fs.labels[fs.nlabels - 1].nactvar = fs.nactvar
    self:checknext(ls, "TK_DOUBLECOLON")
end
function Parser:getlabelname(ls)
    local token = ls.t.token
    if token == "TK_NAME" then
        local name = ls.t.seminfo
        Lexer:next(ls)
        return name
    elseif Lexer.tokens[token] and type(Lexer.tokens[token]) == "string" and #Lexer.tokens[token] > 1 then
        local name = Lexer.tokens[token]
        Lexer:next(ls)
        return name
    else
        Lexer:syntaxerror(ls, "label name expected")
    end
end
function Parser:searchlabel(fs, label)
    for i = 0, fs.nlabels - 1 do
        if fs.labels[i].name == label then
            return fs.labels[i].pc
        end
    end
    return -1
end
function Parser:checkrepeated(fs, label)
    if self:searchlabel(fs, label) >= 0 then
        Lexer:syntaxerror(fs.ls, string.format("label '%s' already defined", label))
    end
end
function Parser:addlabel(fs, label, pc)
    self:growvector(fs.L, fs.labels, fs.nlabels, fs.sizelabels, nil, self.MAX_INT, "too many labels")
    fs.labels[fs.nlabels] = {name = label, pc = pc, nactvar = fs.nactvar}
    fs.nlabels = fs.nlabels + 1
end
function Parser:addpendinggoto(fs, label, pc)
    self:growvector(
        fs.L,
        fs.pendinggotos,
        fs.npendinggotos,
        fs.sizependinggotos,
        nil,
        self.MAX_INT,
        "too many pending gotos"
    )
    fs.pendinggotos[fs.npendinggotos] = {label = label, pc = pc}
    fs.npendinggotos = fs.npendinggotos + 1
end
function Parser:simpleexp(ls, v)
    local c = ls.t.token
    if c == "TK_NUMBER" then
        v.f, v.t = Codegen.NO_JUMP, Codegen.NO_JUMP
        v.k = "VKNUM"
        v.info = 0
        v.nval = ls.t.seminfo
        v.aux = nil
    elseif c == "TK_STRING" then
        self:codestring(ls, v, ls.t.seminfo)
    elseif c == "TK_NIL" then
        v.f, v.t = Codegen.NO_JUMP, Codegen.NO_JUMP
        v.k = "VNIL"
        v.info = 0
        v.nval = nil
        v.aux = nil
    elseif c == "TK_TRUE" then
        v.f, v.t = Codegen.NO_JUMP, Codegen.NO_JUMP
        v.k = "VTRUE"
        v.info = 0
        v.nval = nil
        v.aux = nil
    elseif c == "TK_FALSE" then
        v.f, v.t = Codegen.NO_JUMP, Codegen.NO_JUMP
        v.k = "VFALSE"
        v.info = 0
        v.nval = nil
        v.aux = nil
    elseif c == "TK_DOTS" then
        local fs = ls.fs
        self:check_condition(
            ls,
            fs.f.is_vararg ~= 0,
            "cannot use " .. self:LUA_QL("...") .. " outside a vararg function"
        )
        local is_vararg = fs.f.is_vararg
        if is_vararg >= self.VARARG_NEEDSARG then
            fs.f.is_vararg = is_vararg - self.VARARG_NEEDSARG
        end
        v.f, v.t = Codegen.NO_JUMP, Codegen.NO_JUMP
        v.k = "VVARARG"
        v.info = Codegen:codeABC(fs, "OP_VARARG", 0, 1, 0)
        v.nval = nil
        v.aux = nil
    elseif c == "{" then
        self:constructor(ls, v)
        return
    elseif c == "TK_FUNCTION" then
        Lexer:next(ls)
        self:body(ls, v, false, ls.linenumber)
        return
    else
        self:primaryexp(ls, v)
        return
    end
    Lexer:next(ls)
end
Parser.getbinopr_table = {
    ["+"] = {opr = "OPR_ADD", left = 6, right = 6},
    ["-"] = {opr = "OPR_SUB", left = 6, right = 6},
    ["*"] = {opr = "OPR_MUL", left = 7, right = 7},
    ["/"] = {opr = "OPR_DIV", left = 7, right = 7},
    ["%"] = {opr = "OPR_MOD", left = 7, right = 7},
    ["^"] = {opr = "OPR_POW", left = 10, right = 9},
    ["TK_CONCAT"] = {opr = "OPR_CONCAT", left = 5, right = 4},
    ["TK_NE"] = {opr = "OPR_NE", left = 3, right = 3},
    ["TK_NE2"] = {opr = "OPR_NE", left = 3, right = 3},
    ["TK_EQ"] = {opr = "OPR_EQ", left = 3, right = 3},
    ["<"] = {opr = "OPR_LT", left = 3, right = 3},
    ["TK_LE"] = {opr = "OPR_LE", left = 3, right = 3},
    [">"] = {opr = "OPR_GT", left = 3, right = 3},
    ["TK_GE"] = {opr = "OPR_GE", left = 3, right = 3},
    ["TK_AND"] = {opr = "OPR_AND", left = 2, right = 2},
    ["TK_OR"] = {opr = "OPR_OR", left = 1, right = 1},
    ["TK_ADD2"] = {opr = "OPR_ADD2", left = 6, right = 6},
    ["TK_SUB2"] = {opr = "OPR_SUB2", left = 6, right = 6},
    ["TK_MUL2"] = {opr = "OPR_MUL2", left = 7, right = 7},
    ["TK_DIV2"] = {opr = "OPR_DIV2", left = 7, right = 7},
    ["TK_MOD2"] = {opr = "OPR_MOD2", left = 7, right = 7},
    ["TK_POW2"] = {opr = "OPR_POW2", left = 10, right = 9},
    ["TK_CONCAT2"] = {opr = "OPR_CONCAT2", left = 5, right = 4},
    ["TK_FLOORDIV"] = {opr = "OPR_FLOORDIV", left = 7, right = 7},
    ["TK_FLOORDIV2"] = {opr = "OPR_FLOORDIV2", left = 7, right = 7}
}
function Parser:getbinopr(op)
    local opr = self.getbinopr_table[op]
    if opr then
        return opr
    else
        return "OPR_NOBINOPR"
    end
end
function Parser:getunopr(token)
    if token == "TK_NOT" then
        return "OPR_NOT"
    elseif token == "-" then
        return "OPR_MINUS"
    elseif token == "#" then
        return "OPR_LEN"
    else
        return "OPR_NOUNOPR"
    end
end
Parser.UNARY_PRIORITY = 8
function Parser:subexpr(ls, v, limit)
    Parser:enterlevel(ls)
    local token = ls.t.token
    local uop = self:getunopr(token)
    if uop ~= "OPR_NOUNOPR" then
        Lexer:next(ls)
        Parser:subexpr(ls, v, Parser.UNARY_PRIORITY)
        Codegen:prefix(ls.fs, uop, v)
    else
        Parser:simpleexp(ls, v)
    end
    local binop_info = Parser.getbinopr_table[ls.t.token]
    while binop_info and binop_info.left > limit do
        local op = binop_info.opr
        local v2 = {}
        Lexer:next(ls)
        Codegen:infix(ls.fs, op, v)
        local nextop_info = Parser:subexpr(ls, v2, binop_info.right)
        Codegen:posfix(ls.fs, op, v, v2)
        binop_info = Parser.getbinopr_table[ls.t.token]
    end
    Parser:leavelevel(ls)
    return binop_info and binop_info.opr or "OPR_NOBINOPR"
end
function Parser:expr(ls, v)
    v = v or {f = Codegen.NO_JUMP, t = Codegen.NO_JUMP}
    if ls.t.token == "TK_IF" then
        self:ternary(ls, v)
    else
        self:subexpr(ls, v, 0)
    end
    return v
end
function Parser:block_follow(token)
    if token == "TK_ELSE" or token == "TK_ELSEIF" or token == "TK_END" or token == "TK_UNTIL" or token == "TK_EOS" then
        return true
    else
        return false
    end
end
function Parser:block(ls)
    local fs = ls.fs
    local bl = {}
    self:enterblock(fs, bl, false)
    self:chunk(ls)
    self:leaveblock(fs)
end
function Parser:check_conflict(ls, lh, v)
    local fs = ls.fs
    local extra = fs.freereg
    local conflict = false
    while lh do
        if lh.v.k == "VINDEXED" then
            if lh.v.info == v.info then
                conflict = true
                lh.v.info = extra
            end
            if lh.v.aux == v.info then
                conflict = true
                lh.v.aux = extra
            end
        end
        lh = lh.prev
    end
    if conflict then
        Codegen:codeABC(fs, "OP_MOVE", fs.freereg, v.info, 0)
        Codegen:reserveregs(fs, 1)
    end
end
function Parser:assignment(ls, lh, nvars)
    local e = {}
    local c = lh.v.k
    self:check_condition(ls, c == "VLOCAL" or c == "VUPVAL" or c == "VGLOBAL" or c == "VINDEXED", "syntax error")
    local type_assert = nil
    if self:testnext(ls, "TK_DOUBLECOLON") then
        self:check(ls, "TK_NAME")
        type_assert = ls.t.seminfo
        if not is_valid_type(type_assert) then
            Lexer:syntaxerror(ls, string.format("Invalid type assertion '%s'", type_assert))
        end
        Lexer:next(ls)
    end
    if self:testnext(ls, ",") then
        local nv = {}
        nv.v = {}
        nv.prev = lh
        self:primaryexp(ls, nv.v)
        if nv.v.k == "VLOCAL" then
            self:check_conflict(ls, lh, nv.v)
        end
        self:checklimit(ls.fs, nvars, self.LUAI_MAXCCALLS - ls.L.nCcalls, "variables in assignment")
        self:assignment(ls, nv, nvars + 1)
    elseif type_assert then
        self:checknext(ls, "=")
        local nexps = self:explist1(ls, e)
        if nexps ~= nvars then
            self:adjust_assign(ls, nvars, nexps, e)
            if nexps > nvars then
                ls.fs.freereg = ls.fs.freereg - (nexps - nvars)
            end
        else
            Codegen:setoneret(ls.fs, e)
            local reg = ls.fs.freereg - 1
            emit_type_check(ls.fs, reg, type_assert, ls.linenumber)
            Codegen:storevar(ls.fs, lh.v, e)
            return
        end
    else
        local op = ls.t.token
        local binop_map = {
            TK_ADD2 = "OPR_ADD",
            TK_SUB2 = "OPR_SUB",
            TK_MUL2 = "OPR_MUL",
            TK_DIV2 = "OPR_DIV",
            TK_MOD2 = "OPR_MOD",
            TK_POW2 = "OPR_POW",
            TK_CONCAT2 = "OPR_CONCAT",
            TK_FLOORDIV2 = "OPR_FLOORDIV",
            ["="] = nil
        }
        local binop_str = binop_map[op]
        if binop_str then
            Lexer:next(ls)
            local v = {}
            self:expr(ls, v)
            if lh.v.k == "VINDEXED" then
                local temp = {k = lh.v.k, info = lh.v.info, aux = lh.v.aux}
                local temp_reg = Codegen:exp2anyreg(ls.fs, temp)
                local result = {k = "VNONRELOC", info = temp_reg}
                Codegen:posfix(ls.fs, binop_str, result, v)
                Codegen:storevar(ls.fs, lh.v, result)
            else
                Codegen:posfix(ls.fs, binop_str, lh.v, v)
                Codegen:storevar(ls.fs, lh.v, lh.v)
            end
            return
        elseif op == "=" then
            Lexer:next(ls)
            local nexps = self:explist1(ls, e)
            if nexps ~= nvars then
                self:adjust_assign(ls, nvars, nexps, e)
                if nexps > nvars then
                    ls.fs.freereg = ls.fs.freereg - (nexps - nvars)
                end
            else
                Codegen:setoneret(ls.fs, e)
                Codegen:storevar(ls.fs, lh.v, e)
                return
            end
        else
            Lexer:syntaxerror(ls, "invalid assignment operator")
        end
    end
    self:init_exp(e, "VNONRELOC", ls.fs.freereg - 1)
    Codegen:storevar(ls.fs, lh.v, e)
end
function Parser:cond(ls)
    local v = {}
    self:expr(ls, v)
    if v.k == "VNIL" then
        v.k = "VFALSE"
    end
    Codegen:goiftrue(ls.fs, v)
    return v.f
end
function Parser:breakstat(ls)
    local fs = ls.fs
    local bl = fs.bl
    local upval = false
    while bl and not bl.isbreakable do
        if bl.upval then
            upval = true
        end
        bl = bl.previous
    end
    if not bl then
        Lexer:syntaxerror(ls, "no loop to break")
    end
    if upval then
        Codegen:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
    end
    bl.breaklist = Codegen:concat(fs, bl.breaklist, Codegen:jump(fs))
end
function Parser:continuestat(ls)
    local fs = ls.fs
    local bl = fs.bl
    local upval = false
    while bl and not bl.isbreakable do
        if bl.upval then
            upval = true
        end
        bl = bl.previous
    end
    if not bl then
        Lexer:syntaxerror(ls, "no loop to continue")
    end
    if upval then
        Codegen:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
    end
    local jump = Codegen:jump(fs)
    bl.continuelist = Codegen:concat(fs, bl.continuelist, jump)
end
function Parser:whilestat(ls, line)
    local fs = ls.fs
    local bl = {}
    Lexer:next(ls)
    local whileinit = Codegen:getlabel(fs)
    local condexit = self:cond(ls)
    self:enterblock(fs, bl, true)
    self:checknext(ls, "TK_DO")
    self:block(ls)
    Codegen:patchlist(fs, bl.continuelist, whileinit)
    Codegen:patchlist(fs, Codegen:jump(fs), whileinit)
    self:check_match(ls, "TK_END", "TK_WHILE", line)
    self:leaveblock(fs)
    Codegen:patchtohere(fs, condexit)
end
function Parser:repeatstat(ls, line)
    local fs = ls.fs
    local repeat_init = Codegen:getlabel(fs)
    local bl1, bl2 = {}, {}
    self:enterblock(fs, bl1, true)
    self:enterblock(fs, bl2, false)
    Lexer:next(ls)
    self:chunk(ls)
    self:check_match(ls, "TK_UNTIL", "TK_REPEAT", line)
    local cond_start = fs.pc
    local condexit = self:cond(ls)
    if not bl2.upval then
        self:leaveblock(fs)
        Codegen:patchlist(fs, bl1.continuelist, cond_start)
        Codegen:patchlist(ls.fs, condexit, repeat_init)
    else
        self:breakstat(ls)
        Codegen:patchlist(fs, bl1.continuelist, cond_start)
        Codegen:patchtohere(ls.fs, condexit)
        self:leaveblock(fs)
        Codegen:patchlist(ls.fs, Codegen:jump(fs), repeat_init)
    end
    self:leaveblock(fs)
end
function Parser:valstat(ls)
    local nvars = 0
    local nexps
    local e = {}
    local varnames = {}
    local types = {}
    repeat
        local varname, type_annot = self:checkname(ls, {}, true)
        varnames[nvars + 1] = varname
        types[nvars + 1] = type_annot
        self:new_localvar(ls, varname, nvars, true, false)
        nvars = nvars + 1
    until not self:testnext(ls, ",")
    if self:testnext(ls, "=") then
        nexps = self:explist1(ls, e)
    else
        e.k = "VVOID"
        nexps = 0
    end
    self:adjust_assign(ls, nvars, nexps, e)
    for i = 1, nvars do
        if types[i] then
            local reg = ls.fs.freereg - nvars + i - 1
            emit_type_check(ls.fs, reg, types[i], ls.linenumber)
        end
    end
    self:adjustlocalvars(ls, nvars)
end
function Parser:exp1(ls)
    local e = {}
    self:expr(ls, e)
    local k = e.k
    Codegen:exp2nextreg(ls.fs, e)
    return k
end
function Parser:forbody(ls, base, line, nvars, isnum)
    local bl = {}
    local fs = ls.fs
    self:adjustlocalvars(ls, 3)
    self:checknext(ls, "TK_DO")
    local prep = isnum and Codegen:codeAsBx(fs, "OP_FORPREP", base, Codegen.NO_JUMP) or Codegen:jump(fs)
    self:enterblock(fs, bl, true)
    self:adjustlocalvars(ls, nvars)
    Codegen:reserveregs(fs, nvars)
    self:block(ls)
    self:leaveblock(fs)
    local continue_target = fs.pc
    Codegen:patchtohere(fs, bl.continuelist)
    Codegen:patchtohere(fs, prep)
    local endfor =
        isnum and Codegen:codeAsBx(fs, "OP_FORLOOP", base, Codegen.NO_JUMP) or
        Codegen:codeABC(fs, "OP_TFORLOOP", base, 0, nvars)
    Codegen:fixline(fs, line)
    Codegen:patchlist(fs, isnum and endfor or Codegen:jump(fs), prep + 1)
end
function Parser:fornum(ls, varname, line)
    local fs = ls.fs
    local base = fs.freereg
    self:new_localvarliteral(ls, "(for index)", 0)
    self:new_localvarliteral(ls, "(for limit)", 1)
    self:new_localvarliteral(ls, "(for step)", 2)
    self:new_localvar(ls, varname, 3)
    self:checknext(ls, "=")
    self:exp1(ls)
    self:checknext(ls, ",")
    self:exp1(ls)
    if self:testnext(ls, ",") then
        self:exp1(ls)
    else
        Codegen:codeABx(fs, "OP_LOADK", fs.freereg, Codegen:numberK(fs, 1))
        Codegen:reserveregs(fs, 1)
    end
    self:forbody(ls, base, line, 1, true)
end
function Parser:forlist(ls, indexname)
    local fs = ls.fs
    local e = {}
    local nvars = 0
    local base = fs.freereg
    self:new_localvarliteral(ls, "(for generator)", nvars)
    nvars = nvars + 1
    self:new_localvarliteral(ls, "(for state)", nvars)
    nvars = nvars + 1
    self:new_localvarliteral(ls, "(for control)", nvars)
    nvars = nvars + 1
    self:new_localvar(ls, indexname, nvars)
    nvars = nvars + 1
    while self:testnext(ls, ",") do
        self:new_localvar(ls, self:str_checkname(ls), nvars)
        nvars = nvars + 1
    end
    self:checknext(ls, "TK_IN")
    local line = ls.linenumber
    self:adjust_assign(ls, 3, self:explist1(ls, e), e)
    Codegen:checkstack(fs, 3)
    self:forbody(ls, base, line, nvars - 3, false)
end
function Parser:forstat(ls, line)
    local fs = ls.fs
    local bl = {}
    self:enterblock(fs, bl, true)
    Lexer:next(ls)
    local varname = self:str_checkname(ls)
    local c = ls.t.token
    if c == "=" then
        self:fornum(ls, varname, line)
    elseif c == "," or c == "TK_IN" then
        self:forlist(ls, varname)
    else
        Lexer:syntaxerror(ls, self:LUA_QL("=") .. " or " .. self:LUA_QL("in") .. " expected")
    end
    self:check_match(ls, "TK_END", "TK_FOR", line)
    self:leaveblock(fs)
end
function Parser:test_then_block(ls)
    Lexer:next(ls)
    local condexit = self:cond(ls)
    self:checknext(ls, "TK_THEN")
    self:block(ls)
    return condexit
end
function Parser:ifstat(ls, line)
    local fs = ls.fs
    local escapelist = Codegen.NO_JUMP
    local flist = self:test_then_block(ls)
    while ls.t.token == "TK_ELSEIF" do
        escapelist = Codegen:concat(fs, escapelist, Codegen:jump(fs))
        Codegen:patchtohere(fs, flist)
        flist = self:test_then_block(ls)
    end
    if ls.t.token == "TK_ELSE" then
        escapelist = Codegen:concat(fs, escapelist, Codegen:jump(fs))
        Codegen:patchtohere(fs, flist)
        Lexer:next(ls)
        self:block(ls)
    else
        escapelist = Codegen:concat(fs, escapelist, flist)
    end
    Codegen:patchtohere(fs, escapelist)
    self:check_match(ls, "TK_END", "TK_IF", line)
end
function Parser:localfunc(ls)
    local v, b = {}, {}
    local fs = ls.fs
    self:new_localvar(ls, self:str_checkname(ls), 0)
    self:init_exp(v, "VLOCAL", fs.freereg)
    Codegen:reserveregs(fs, 1)
    self:adjustlocalvars(ls, 1)
    self:body(ls, b, false, ls.linenumber)
    Codegen:storevar(fs, v, b)
    self:getlocvar(fs, fs.nactvar - 1).startpc = fs.pc
end
function Parser:ternary(ls, v)
    self:enterlevel(ls)
    local line = ls.linenumber
    Lexer:next(ls)
    local cond = {}
    self:expr(ls, cond)
    Codegen:goiftrue(ls.fs, cond)
    self:checknext(ls, "TK_THEN")
    local v_true = {}
    self:subexpr(ls, v_true, 0)
    Codegen:exp2nextreg(ls.fs, v_true)
    local result_reg = v_true.info
    local jump_to_else = Codegen:jump(ls.fs)
    Codegen:patchtohere(ls.fs, cond.f)
    local v_false = {}
    while ls.t.token == "TK_ELSEIF" do
        Lexer:next(ls)
        local elseif_cond = {}
        self:expr(ls, elseif_cond)
        Codegen:goiftrue(ls.fs, elseif_cond)
        self:checknext(ls, "TK_THEN")
        local elseif_val = {}
        self:subexpr(ls, elseif_val, 0)
        Codegen:exp2nextreg(ls.fs, elseif_val)
        local elseif_reg = elseif_val.info
        if elseif_reg ~= result_reg then
            Codegen:codeABC(ls.fs, "OP_MOVE", result_reg, elseif_reg, 0)
            Codegen:freereg(ls.fs, elseif_reg)
        end
        jump_to_else = Codegen:concat(ls.fs, jump_to_else, Codegen:jump(ls.fs))
        Codegen:patchtohere(ls.fs, elseif_cond.f)
    end
    self:checknext(ls, "TK_ELSE")
    self:subexpr(ls, v_false, 0)
    Codegen:exp2nextreg(ls.fs, v_false)
    local false_reg = v_false.info
    if false_reg ~= result_reg then
        Codegen:codeABC(ls.fs, "OP_MOVE", result_reg, false_reg, 0)
        Codegen:freereg(ls.fs, false_reg)
    end
    local end_jump = Codegen:jump(ls.fs)
    Codegen:patchtohere(ls.fs, jump_to_else)
    self:init_exp(v, "VNONRELOC", result_reg)
    v.t = Codegen.NO_JUMP
    v.f = Codegen.NO_JUMP
    Codegen:patchtohere(ls.fs, end_jump)
    self:leavelevel(ls)
end
function Parser:localstat(ls)
    local nvars = 0
    local nexps
    local e = {}
    local varnames = {}
    local types = {}
    repeat
        local varname, type_annot = self:checkname(ls, {}, true)
        local is_const = false
        local is_close = false
        if ls.t.token == "<" then
            Lexer:next(ls)
            self:check(ls, "TK_NAME")
            local attr = ls.t.seminfo
            if attr == "const" then
                is_const = true
            elseif attr == "close" then
                is_close = true
            else
                Lexer:syntaxerror(ls, "Invalid attribute '" .. attr .. "'")
            end
            Lexer:next(ls)
            self:checknext(ls, ">")
        end
        varnames[nvars + 1] = varname
        types[nvars + 1] = type_annot
        self:new_localvar(ls, varname, nvars, is_const, is_close)
        nvars = nvars + 1
    until not self:testnext(ls, ",")
    if self:testnext(ls, "=") then
        nexps = self:explist1(ls, e)
    else
        e.k = "VVOID"
        nexps = 0
    end
    if ls.t.token == "TK_DOUBLECOLON" then
        Lexer:next(ls)
        self:check(ls, "TK_NAME")
        local type_assert = ls.t.seminfo
        if not is_valid_type(type_assert) then
            Lexer:syntaxerror(ls, string.format("Invalid type assertion '%s'", type_assert))
        end
        Lexer:next(ls)
        if nexps == 1 and nvars == 1 then
            Codegen:setoneret(ls.fs, e)
            local reg = ls.fs.freereg - 1
            emit_type_check(ls.fs, reg, type_assert, ls.linenumber)
        end
    end
    self:adjust_assign(ls, nvars, nexps, e)
    for i = 1, nvars do
        if types[i] then
            local reg = ls.fs.freereg - nvars + i - 1
            emit_type_check(ls.fs, reg, types[i], ls.linenumber)
        end
    end
    self:adjustlocalvars(ls, nvars)
end
function Parser:funcname(ls, v)
    local needself = false
    self:singlevar(ls, v)
    while ls.t.token == "." do
        self:field(ls, v)
    end
    if ls.t.token == ":" then
        needself = true
        self:field(ls, v)
    end
    if ls.t.token == ":" then
        Lexer:next(ls)
        self:check(ls, "TK_NAME")
        local return_type = ls.t.seminfo
        if not is_valid_type(return_type) then
            Lexer:syntaxerror(ls, string.format("Invalid return type '%s'", return_type))
        end
        Lexer:next(ls)
        v.return_type = return_type
    end
    return needself
end
function Parser:funcstat(ls, line)
    local v, b = {}, {}
    Lexer:next(ls)
    local needself = self:funcname(ls, v)
    self:body(ls, b, needself, line)
    Codegen:storevar(ls.fs, v, b)
    Codegen:fixline(ls.fs, line)
end
function Parser:exprstat(ls)
    local fs = ls.fs
    local v = {}
    v.v = {}
    self:primaryexp(ls, v.v)
    if ls.t.token == "TK_DOUBLECOLON" then
        Lexer:next(ls)
        self:check(ls, "TK_NAME")
        local type_assert = ls.t.seminfo
        if not is_valid_type(type_assert) then
            Lexer:syntaxerror(ls, string.format("Invalid type assertion '%s'", type_assert))
        end
        Lexer:next(ls)
        local reg = Codegen:exp2anyreg(fs, v.v)
        emit_type_check(fs, reg, type_assert, ls.linenumber)
    elseif v.v.k == "VCALL" then
        Instruction:SETARG_C(Codegen:getcode(fs, v.v), 1)
    else
        v.prev = nil
        self:assignment(ls, v, 1)
    end
end
function Parser:retstat(ls)
    local fs = ls.fs
    local e = {}
    local first, nret
    Lexer:next(ls)
    if self:block_follow(ls.t.token) or ls.t.token == ";" then
        first, nret = 0, 0
    else
        nret = self:explist1(ls, e)
        if self:hasmultret(e.k) then
            Codegen:setmultret(fs, e)
            if e.k == "VCALL" and nret == 1 then
                Instruction:SET_OPCODE(Codegen:getcode(fs, e), "OP_TAILCALL")
            end
            first = fs.nactvar
            nret = self.LUA_MULTRET
        else
            if nret == 1 then
                first = Codegen:exp2anyreg(fs, e)
            else
                Codegen:exp2nextreg(fs, e)
                first = fs.nactvar
            end
        end
    end
    Codegen:ret(fs, first, nret)
end
local statement_handlers = {
    TK_IF = Parser.ifstat,
    TK_WHILE = Parser.whilestat,
    TK_DO = function(self, ls, line)
        Lexer:next(ls)
        self:block(ls)
        self:check_match(ls, "TK_END", "TK_DO", line)
        return false
    end,
    TK_FOR = Parser.forstat,
    TK_REPEAT = Parser.repeatstat,
    TK_FUNCTION = Parser.funcstat,
    TK_LOCAL = function(self, ls)
        Lexer:next(ls)
        if self:testnext(ls, "TK_FUNCTION") then
            self:localfunc(ls)
        else
            self:localstat(ls)
        end
        return false
    end,
    TK_VAL = function(self, ls)
        Lexer:next(ls)
        self:valstat(ls)
        return false
    end,
    TK_RETURN = Parser.retstat,
    TK_BREAK = function(self, ls)
        Lexer:next(ls)
        self:breakstat(ls)
        return true
    end,
    TK_CONTINUE = function(self, ls)
        Lexer:next(ls)
        self:continuestat(ls)
        return true
    end,
    TK_GOTO = function(self, ls)
        Lexer:next(ls)
        self:gotostat(ls)
        return true
    end,
    TK_DOUBLECOLON = function(self, ls)
        Lexer:next(ls)
        self:labelstat(ls, self:str_checkname(ls), ls.linenumber)
        return false
    end
}
function Parser:statement(ls)
    local line = ls.linenumber
    local token = ls.t.token
    if token == "TK_NAME" and ls.t.seminfo == "type" then
        Lexer:lookahead(ls)
        if ls.lookahead.token == "TK_NAME" then
            Lexer:next(ls)
            self:check(ls, "TK_NAME")
            local type_name = ls.t.seminfo
            Lexer:next(ls)
            self:checknext(ls, "=")
            if ls.t.token == "TK_NAME" then
                local type_def = ls.t.seminfo
                if not is_valid_type(type_def) then
                    Lexer:syntaxerror(ls, string.format("Invalid type definition '%s'", type_def))
                end
                Lexer:next(ls)
            elseif ls.t.token == "{" then
                local fields = {}
                Lexer:next(ls)
                while ls.t.token ~= "}" do
                    self:check(ls, "TK_NAME")
                    local field_name = ls.t.seminfo
                    Lexer:next(ls)
                    self:checknext(ls, ":")
                    self:check(ls, "TK_NAME")
                    local field_type = ls.t.seminfo
                    if not is_valid_type(field_type) then
                        Lexer:syntaxerror(ls, string.format("Invalid field type '%s'", field_type))
                    end
                    fields[field_name] = field_type
                    Lexer:next(ls)
                    if ls.t.token == "," then
                        Lexer:next(ls)
                    end
                end
                Lexer:next(ls)
            else
                Lexer:syntaxerror(ls, "Invalid type definition")
            end
            return false
        else
            self:exprstat(ls)
            return false
        end
    end
    local handler = statement_handlers[token]
    if handler then
        return handler(self, ls, line)
    else
        self:exprstat(ls)
        return false
    end
end
function Parser:chunk(ls)
    local islast = false
    self:enterlevel(ls)
    while not self:block_follow(ls.t.token) do
        islast = self:statement(ls)
        self:testnext(ls, ";")
        ls.fs.freereg = ls.fs.nactvar
    end
    self:leavelevel(ls)
end
Lexer:init()
local LuaState = {}
function compile(source, name)
    name = name or "compiled-lua"
    local zio = Buffer:init(source)
    if not zio then
        error("Failed to initialize input buffer")
    end
    local LuaState = {}
    local func = Parser:parser(LuaState, zio, nil, "@" .. name)
    local writer, buff = Serializer:make_setS()
    local status = Serializer:dump(LuaState, func, writer, buff)
    if status ~= 0 then
        error("Failed to serialize bytecode")
    end
    return buff.data
end
return compile

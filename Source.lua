--[[
  Zuexiang (ZX / ZueX / YueliangX)
  A fork of the Yueliang Lua 5.1 compiler, with extended features and optimizations.

  Original base project:
    Yueliang - Lua 5.1 Bytecode Compiler
    Author: Kein-Hong man
    Source: http://yueliang.luaforge.net/

  Modifications and extensions by:
    Nyreel

  This version includes:
    - Support for 'goto' and 'continue'
    - Compound assignment (+=, -=, etc.)
    - '!=' alias for '~='
    - Luau-style number literals
    - Ternary expressions in local declarations
    - Integer division operator (//)
    - Parser and performance improvements

  License:
    MIT License (same as original Yueliang)

  Note:
    This is not an official continuation of Yueliang. It’s a personal project made
    for experimentation, learning, and fun. Expect messy code and fast hacks.
]]

local luaZ, luaY, luaK, luaU, luaK = {}, {}, {}, {}, {}
function luaZ:init(reader, data)
    if not reader then
        return
    end
    data = data or ""
    return {reader = reader, data = data, name = "", n = #data, p = 0}
end
function luaZ:make_getF(source)
    local pos, buffer = 1, ""
    return function()
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
    end
end
function luaZ:fill(z)
    z.data = z.reader() or ""
    z.n, z.p = #z.data - 1, 1
    return z.n >= 0 and z.data:sub(1, 1) or "EOZ"
end
luaK.RESERVED =
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
    TK_NAME <name>
    TK_NUMBER <number>
    TK_STRING <string>
    TK_EOS <eof>
]]
luaK.MAXSRC = 80
luaK.MAX_INT = 2147483645
luaK.LUA_COMPAT_LSTR = 1
function luaK:init()
    local tokens, enums = {}, {}
    for tok, str in self.RESERVED:gmatch("(%S+)%s+(%S+)") do
        tokens[tok], enums[str] = str, tok
    end
    self.tokens, self.enums = tokens, enums
end
function luaK:chunkid(source, bufflen)
    local first, len = source:sub(1, 1), bufflen - 3
    if first == "=" then
        return source:sub(2, len + 1)
    end
    source = first == "@" and source:sub(2) or source:sub(1, (source:find("[\n\r]") or #source + 1) - 1)
    len = math.min(len + 1, #source)
    source = #source > len and "..." .. source:sub(-len) or ('[string "%s"]'):format(source)
    return source
end
function luaK:token2str(token)
    local t = self.tokens[token]
    return t or type(token) == string and (token:match("%c") and ("char(%d)"):format(token:byte())) or token
end
function luaK:lexerror(ls, msg, token)
    local txtToken =
        token == "TK_NAME" or token == "TK_STRING" or token == "TK_NUMBER" and ls.buff or self:token2str(token)
    local line, context = ls.linenumber, ls.buff or ls.current or "<unknown>"
    error(
        ("%s:%d: %s (near '%s')%s"):format(
            self:chunkid(ls.source, self.MAXSRC),
            line,
            msg,
            context,
            token and ", token: " .. txtToken or ""
        )
    )
end
function luaK:syntaxerror(ls, msg)
    self:lexerror(ls, msg, ls.t.token)
end
function luaK:currIsNewline(ls)
    return ls.current == "\n" or ls.current == "\r"
end
function luaK:inclinenumber(ls)
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
function luaK:setinput(L, ls, z, source)
    ls = ls or {}
    ls.lookahead, ls.t = ls.lookahead or {}, ls.t or {}
    ls.decpoint, ls.L = ".", L
    ls.lookahead.token = "TK_EOS"
    ls.z, ls.fs = z, nil
    ls.linenumber, ls.lastline = 1, 1
    ls.source = source
    self:nextc(ls)
end
function luaK:check_next(ls, set)
    if not set:find(ls.current, 1, true) then
        return false
    end
    self:save_and_next(ls)
    return true
end
function luaK:next(ls)
    ls.lastline = ls.linenumber
    if ls.lookahead.token ~= "TK_EOS" then
        ls.t.token, ls.t.seminfo = ls.lookahead.token, ls.lookahead.seminfo
        ls.lookahead.token = "TK_EOS"
    else
        ls.t.token = self:llex(ls, ls.t)
    end
end
function luaK:lookahead(ls)
    ls.lookahead.token = self:llex(ls, ls.lookahead)
end
function luaK:nextc(ls)
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
function luaK:save(ls, c)
    ls.buff = (ls.buff or "") .. c
end
function luaK:save_and_next(ls)
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
function luaK:buffreplace(ls, from, to)
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
function luaK:trydecpoint(ls, Token)
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
function luaK:read_numeral(ls, Token)
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
function luaK:read_long_string(ls, Token, sep)
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
function luaK:read_string(ls, del, Token)
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
function luaK:skip_sep(ls)
    local count = 0
    local s = ls.current
    self:save_and_next(ls)
    while ls.current == "=" do
        self:save_and_next(ls)
        count = count + 1
    end
    return (ls.current == s) and count or (-count) - 1
end
function luaK:llex(ls, Token)
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
local luaP = {
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
local OpCode, ROpCode, opname = luaP.OpCode, luaP.ROpCode, luaP.opnames
for i = 0, #opnames - 1 do
    local name = "OP_" .. opnames[i + 1]
    opname[i] = opnames[i + 1]
    OpCode[name], ROpCode[i] = i, name
end
luaP.NUM_OPCODES = #opnames
luaP.OpArgMask = {OpArgN = 0, OpArgU = 1, OpArgR = 2, OpArgK = 3}
local function opmode(t, a, b, c, m)
    return t * 128 + a * 64 + luaP.OpArgMask[b] * 16 + luaP.OpArgMask[c] * 4 + luaP.OpMode[m]
end
luaP.opmodes = {
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
luaP.opmodes[0] = opmode(0, 1, "OpArgR", "OpArgN", "iABC")
function luaP:GET_OPCODE(i)
    return self.ROpCode[i.OP]
end
function luaP:SET_OPCODE(i, o)
    i.OP = self.OpCode[o]
end
function luaP:GETARG_A(i)
    return i.A
end
function luaP:SETARG_A(i, a)
    i.A = a
end
function luaP:GETARG_B(i)
    return i.B
end
function luaP:SETARG_B(i, b)
    i.B = b
end
function luaP:GETARG_C(i)
    return i.C
end
function luaP:SETARG_C(i, c)
    i.C = c
end
function luaP:GETARG_Bx(i)
    return i.Bx
end
function luaP:SETARG_Bx(i, bx)
    i.Bx = bx
end
function luaP:GETARG_sBx(i)
    return i.Bx - self.MAXARG_sBx
end
function luaP:SETARG_sBx(i, sbx)
    i.Bx = sbx + self.MAXARG_sBx
end
function luaP:CREATE_ABC(o, a, b, c)
    return {OP = self.OpCode[o], A = a, B = b, C = c}
end
function luaP:CREATE_ABx(o, a, bc)
    return {OP = self.OpCode[o], A = a, Bx = bc}
end
function luaP:CREATE_Inst(code)
    local o = code % 64
    local a = (code - o) / 64 % 256
    local bx = (code - o - a * 64) / 16384
    return self:CREATE_ABx(o, a, bx)
end
function luaP:Instruction(i)
    if i.Bx then
        i.C = i.Bx % 512
        i.B = (i.Bx - i.C) / 512
    end
    local v = i.A * 64 + i.OP
    local c0 = v % 256
    v = (v - c0) / 256 + i.C * 64
    local c1 = v % 256
    v = (v - c1) / 256 + i.B * 128
    local c2 = v % 256
    local c3 = (v - c2) / 256
    return string.char(c0, c1, c2, c3)
end
function luaP:DecodeInst(x)
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
function luaP:ISK(x)
    return x >= self.BITRK
end
function luaP:INDEXK(r)
    return r - self.BITRK
end
function luaP:RKASK(x)
    return x + self.BITRK
end
function luaP:getOpMode(m)
    return self.opmodes[self.OpCode[m]] % 4
end
function luaP:getBMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 16) % 4
end
function luaP:getCMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 4) % 4
end
function luaP:testAMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 64) % 2
end
function luaP:testTMode(m)
    return math.floor(self.opmodes[self.OpCode[m]] / 128)
end
luaP.LFIELDS_PER_FLUSH = 50
luaU.LUA_SIGNATURE = "\27Lua"
luaU.LUA_TNUMBER = 3
luaU.LUA_TSTRING = 4
luaU.LUA_TNIL = 0
luaU.LUA_TBOOLEAN = 1
luaU.LUA_TNONE = -1
luaU.LUAC_VERSION = 81
luaU.LUAC_FORMAT = 0
luaU.LUAC_HEADERSIZE = 12
function luaU:make_setS()
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
function luaU:make_setF(filename)
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
function luaU:ttype(o)
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
function luaU:from_double(x)
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
function luaU:from_int(x)
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
function luaU:DumpBlock(b, D)
    if D.status == 0 then
        D.status = D.write(b, D.data)
    end
end
function luaU:DumpChar(y, D)
    self:DumpBlock(string.char(y), D)
end
function luaU:DumpInt(x, D)
    self:DumpBlock(self:from_int(x), D)
end
function luaU:DumpSizeT(x, D)
    self:DumpBlock(self:from_int(x), D)
    self:DumpBlock(self:from_int(0), D)
end
function luaU:DumpNumber(x, D)
    self:DumpBlock(self:from_double(x), D)
end
function luaU:DumpString(s, D)
    if s == nil then
        self:DumpSizeT(0, D)
    else
        self:DumpSizeT(#s + 1, D)
        self:DumpBlock(s .. "\0", D)
    end
end
function luaU:DumpCode(f, D)
    local n = f.sizecode
    self:DumpInt(n, D)
    local chunks = {}
    for i = 0, n - 1 do
        chunks[i + 1] = luaP:Instruction(f.code[i])
    end
    self:DumpBlock(table.concat(chunks), D)
end
function luaU:DumpConstants(f, D)
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
function luaU:DumpDebug(f, D)
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
function luaU:DumpFunction(f, p, D)
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
function luaU:DumpHeader(D)
    local h = self:header()
    assert(#h == self.LUAC_HEADERSIZE)
    self:DumpBlock(h, D)
end
function luaU:header()
    local x = 1
    return self.LUA_SIGNATURE .. string.char(self.LUAC_VERSION, self.LUAC_FORMAT, x, 4, 8, 4, 8, 0)
end
function luaU:dump(L, f, w, data, strip)
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
luaK.MAXSTACK = 250
function luaK:ttisnumber(o)
    return o and type(o.value) == "number" or false
end
function luaK:nvalue(o)
    return o.value
end
function luaK:setnilvalue(o)
    o.value = nil
end
function luaK:setsvalue(o, x)
    o.value = x
end
luaK.setnvalue = luaK.setsvalue
luaK.sethvalue = luaK.setsvalue
luaK.setbvalue = luaK.setsvalue
function luaK:numadd(a, b)
    return a + b
end
function luaK:numsub(a, b)
    return a - b
end
function luaK:nummul(a, b)
    return a * b
end
function luaK:numdiv(a, b)
    return a / b
end
function luaK:nummod(a, b)
    return a % b
end
function luaK:numpow(a, b)
    return a ^ b
end
function luaK:numunm(a)
    return -a
end
function luaK:numisnan(a)
    return a ~= a
end
luaK.NO_JUMP = -1
luaK.BinOpr = {
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
luaK.UnOpr = {OPR_MINUS = 0, OPR_NOT = 1, OPR_LEN = 2, OPR_NOUNOPR = 3}
function luaK:getcode(fs, e)
    return fs.f.code[e.info]
end
function luaK:codeAsBx(fs, o, A, sBx)
    return self:codeABx(fs, o, A, sBx + luaP.MAXARG_sBx)
end
function luaK:setmultret(fs, e)
    self:setreturns(fs, e, luaY.LUA_MULTRET)
end
function luaK:hasjumps(e)
    return e.t ~= e.f
end
function luaK:isnumeral(e)
    return e.k == "VKNUM" and e.t == self.NO_JUMP and e.f == self.NO_JUMP
end
function luaK:_nil(fs, from, n)
    if fs.pc > fs.lasttarget then
        if fs.pc == 0 then
            if from >= fs.nactvar then
                return
            end
        else
            local previous = fs.f.code[fs.pc - 1]
            if luaP:GET_OPCODE(previous) == "OP_LOADNIL" then
                local pfrom = luaP:GETARG_A(previous)
                local pto = luaP:GETARG_B(previous)
                if pfrom <= from and from <= pto + 1 then
                    if from + n - 1 > pto then
                        luaP:SETARG_B(previous, from + n - 1)
                    end
                    return
                end
            end
        end
    end
    self:codeABC(fs, "OP_LOADNIL", from, from + n - 1, 0)
end
function luaK:jump(fs)
    local jpc = fs.jpc
    fs.jpc = self.NO_JUMP
    local j = self:codeAsBx(fs, "OP_JMP", 0, self.NO_JUMP)
    j = self:concat(fs, j, jpc)
    return j
end
function luaK:ret(fs, first, nret)
    self:codeABC(fs, "OP_RETURN", first, nret + 1, 0)
end
function luaK:condjump(fs, op, A, B, C)
    self:codeABC(fs, op, A, B, C)
    return self:jump(fs)
end
function luaK:fixjump(fs, pc, dest)
    local jmp = fs.f.code[pc]
    local offset = dest - (pc + 1)
    if math.abs(offset) > luaP.MAXARG_sBx then
        luaK:syntaxerror(fs.ls, "control structure too long")
    end
    luaP:SETARG_sBx(jmp, offset)
end
function luaK:getlabel(fs)
    fs.lasttarget = fs.pc
    return fs.pc
end
function luaK:getjump(fs, pc)
    local offset = luaP:GETARG_sBx(fs.f.code[pc])
    if offset == self.NO_JUMP then
        return self.NO_JUMP
    else
        return (pc + 1) + offset
    end
end
function luaK:getjumpcontrol(fs, pc)
    local pi = fs.f.code[pc]
    local ppi = fs.f.code[pc - 1]
    if pc >= 1 and luaP:testTMode(luaP:GET_OPCODE(ppi)) ~= 0 then
        return ppi
    else
        return pi
    end
end
function luaK:need_value(fs, list)
    while list ~= self.NO_JUMP do
        local i = self:getjumpcontrol(fs, list)
        if luaP:GET_OPCODE(i) ~= "OP_TESTSET" then
            return true
        end
        list = self:getjump(fs, list)
    end
    return false
end
function luaK:patchtestreg(fs, node, reg)
    local i = self:getjumpcontrol(fs, node)
    if luaP:GET_OPCODE(i) ~= "OP_TESTSET" then
        return false
    end
    if reg ~= luaP.NO_REG and reg ~= luaP:GETARG_B(i) then
        luaP:SETARG_A(i, reg)
    else
        luaP:SET_OPCODE(i, "OP_TEST")
        local b = luaP:GETARG_B(i)
        luaP:SETARG_A(i, b)
        luaP:SETARG_B(i, 0)
    end
    return true
end
function luaK:removevalues(fs, list)
    while list ~= self.NO_JUMP do
        self:patchtestreg(fs, list, luaP.NO_REG)
        list = self:getjump(fs, list)
    end
end
function luaK:patchlistaux(fs, list, vtarget, reg, dtarget)
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
function luaK:dischargejpc(fs)
    self:patchlistaux(fs, fs.jpc, fs.pc, luaP.NO_REG, fs.pc)
    fs.jpc = self.NO_JUMP
end
function luaK:patchlist(fs, list, target)
    if target == fs.pc then
        self:patchtohere(fs, list)
    else
        self:patchlistaux(fs, list, target, luaP.NO_REG, target)
    end
end
function luaK:patchtohere(fs, list)
    self:getlabel(fs)
    fs.jpc = self:concat(fs, fs.jpc, list)
end
function luaK:concat(fs, l1, l2)
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
function luaK:checkstack(fs, n)
    local newstack = fs.freereg + n
    if newstack > fs.f.maxstacksize then
        if newstack >= self.MAXSTACK then
            luaK:syntaxerror(fs.ls, "function or expression too complex")
        end
        fs.f.maxstacksize = newstack
    end
end
function luaK:reserveregs(fs, n)
    self:checkstack(fs, n)
    fs.freereg = fs.freereg + n
end
function luaK:freereg(fs, reg)
    if not luaP:ISK(reg) and reg >= fs.nactvar then
        fs.freereg = fs.freereg - 1
    end
end
function luaK:freeexp(fs, e)
    if e.k == "VNONRELOC" then
        self:freereg(fs, e.info)
    end
end
function luaK:addk(fs, k, v)
    local idx = fs.h[k.value]
    if self:ttisnumber(idx) then
        return self:nvalue(idx)
    end
    idx = {}
    self:setnvalue(idx, fs.nk)
    fs.h[k.value] = idx
    luaY:growvector(fs.L, fs.f.k, fs.nk, fs.f.sizek, nil, luaP.MAXARG_Bx, "constant table overflow")
    fs.f.k[fs.nk] = v
    fs.nk = fs.nk + 1
    return fs.nk - 1
end
function luaK:stringK(fs, s)
    local o = {}
    self:setsvalue(o, s)
    return self:addk(fs, o, o)
end
function luaK:numberK(fs, r)
    local o = {}
    self:setnvalue(o, r)
    return self:addk(fs, o, o)
end
function luaK:boolK(fs, b)
    local o = {}
    self:setbvalue(o, b)
    return self:addk(fs, o, o)
end
function luaK:nilK(fs)
    local k, v = {}, {}
    self:setnilvalue(v)
    self:sethvalue(k, fs.h)
    return self:addk(fs, k, v)
end
function luaK:setreturns(fs, e, nresults)
    if e.k == "VCALL" then
        luaP:SETARG_C(self:getcode(fs, e), nresults + 1)
    elseif e.k == "VVARARG" then
        luaP:SETARG_B(self:getcode(fs, e), nresults + 1)
        luaP:SETARG_A(self:getcode(fs, e), fs.freereg)
        luaK:reserveregs(fs, 1)
    end
end
function luaK:setoneret(fs, e)
    if e.k == "VCALL" then
        e.k = "VNONRELOC"
        e.info = luaP:GETARG_A(self:getcode(fs, e))
    elseif e.k == "VVARARG" then
        luaP:SETARG_B(self:getcode(fs, e), 2)
        e.k = "VRELOCABLE"
    end
end
function luaK:dischargevars(fs, e)
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
function luaK:code_label(fs, A, b, jump)
    self:getlabel(fs)
    return self:codeABC(fs, "OP_LOADBOOL", A, b, jump)
end
function luaK:discharge2reg(fs, e, reg)
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
function luaK:discharge2anyreg(fs, e)
    if e.k ~= "VNONRELOC" then
        self:reserveregs(fs, 1)
        self:discharge2reg(fs, e, fs.freereg - 1)
    end
end
function luaK:exp2reg(fs, e, reg)
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
function luaK:exp2nextreg(fs, e)
    self:dischargevars(fs, e)
    self:freeexp(fs, e)
    self:reserveregs(fs, 1)
    self:exp2reg(fs, e, fs.freereg - 1)
end
function luaK:exp2anyreg(fs, e)
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
function luaK:exp2val(fs, e)
    if self:hasjumps(e) then
        self:exp2anyreg(fs, e)
    else
        self:dischargevars(fs, e)
    end
end
function luaK:exp2RK(fs, e)
    luaK:exp2val(fs, e)
    local k = e.k
    if k == "VKNUM" or k == "VTRUE" or k == "VFALSE" or k == "VNIL" then
        if fs.nk <= luaP.MAXINDEXRK then
            if k == "VNIL" then
                local o = {}
                luaK:setnilvalue(o)
                local k_obj = {}
                luaK:sethvalue(k_obj, fs.h)
                e.info = luaK:addk(fs, k_obj, o)
            else
                e.info = (k == "VKNUM") and luaK:numberK(fs, e.nval) or luaK:boolK(fs, k == "VTRUE")
            end
            e.k = "VK"
            return luaP:RKASK(e.info)
        end
    elseif k == "VK" and e.info <= luaP.MAXINDEXRK then
        return luaP:RKASK(e.info)
    end
    return luaK:exp2anyreg(fs, e)
end
function luaK:storevar(fs, var, ex)
    local k = var.k
    if k == "VLOCAL" then
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
function luaK:_self(fs, e, key)
    self:exp2anyreg(fs, e)
    self:freeexp(fs, e)
    local func = fs.freereg
    self:reserveregs(fs, 2)
    self:codeABC(fs, "OP_SELF", func, e.info, self:exp2RK(fs, key))
    self:freeexp(fs, key)
    e.info = func
    e.k = "VNONRELOC"
end
function luaK:invertjump(fs, e)
    local pc = self:getjumpcontrol(fs, e.info)
    luaP:SETARG_A(pc, (luaP:GETARG_A(pc) == 0) and 1 or 0)
end
function luaK:jumponcond(fs, e, cond)
    if e.k == "VRELOCABLE" then
        local ie = self:getcode(fs, e)
        if luaP:GET_OPCODE(ie) == "OP_NOT" then
            fs.pc = fs.pc - 1
            return self:condjump(fs, "OP_TEST", luaP:GETARG_B(ie), 0, cond and 0 or 1)
        end
    end
    self:discharge2anyreg(fs, e)
    self:freeexp(fs, e)
    return self:condjump(fs, "OP_TESTSET", luaP.NO_REG, e.info, cond and 1 or 0)
end
function luaK:goiftrue(fs, e)
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
function luaK:goiffalse(fs, e)
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
function luaK:codenot(fs, e)
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
function luaK:indexed(fs, t, k)
    t.aux = self:exp2RK(fs, k)
    t.k = "VINDEXED"
end
function luaK:code_floor(fs, src_reg, dest_reg)
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
function luaK:constfolding(op, e1, e2)
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
function luaK:codearith(fs, op, e1, e2)
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
function luaK:codecomp(fs, op, cond, e1, e2)
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
function luaK:prefix(fs, op, e)
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
function luaK:infix(fs, op, v)
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
luaK.arith_op = {
    OPR_ADD = "OP_ADD",
    OPR_SUB = "OP_SUB",
    OPR_MUL = "OP_MUL",
    OPR_DIV = "OP_DIV",
    OPR_MOD = "OP_MOD",
    OPR_POW = "OP_POW",
    OPR_FLOORDIV = "OP_FLOORDIV"
}
luaK.comp_op = {
    OPR_EQ = "OP_EQ",
    OPR_NE = "OP_EQ",
    OPR_LT = "OP_LT",
    OPR_LE = "OP_LE",
    OPR_GT = "OP_LT",
    OPR_GE = "OP_LE"
}
luaK.comp_cond = {OPR_EQ = 1, OPR_NE = 0, OPR_LT = 1, OPR_LE = 1, OPR_GT = 0, OPR_GE = 0}
function luaK:posfix(fs, op, e1, e2)
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
        if e2.k == "VRELOCABLE" and luaP:GET_OPCODE(self:getcode(fs, e2)) == "OP_CONCAT" then
            self:freeexp(fs, e1)
            luaP:SETARG_B(self:getcode(fs, e2), e1.info)
            e1.k = "VRELOCABLE"
            e1.info = e2.info
        else
            self:exp2nextreg(fs, e2)
            self:codearith(fs, "OP_CONCAT", e1, e2)
        end
    else
        local arith = self.arith_op[op] or self.arith_op[string.gsub(op, "2", "")]
        if arith then
            self:codearith(fs, arith, e1, e2)
        else
            local comp = self.comp_op[op]
            if comp then
                self:codecomp(fs, comp, self.comp_cond[op], e1, e2)
            else
            end
        end
    end
end
function luaK:fixline(fs, line)
    fs.f.lineinfo[fs.pc - 1] = line
end
function luaK:code(fs, i, line)
    local f = fs.f
    self:dischargejpc(fs)
    luaY:growvector(fs.L, f.code, fs.pc, f.sizecode, nil, luaY.MAX_INT, "code size overflow")
    f.code[fs.pc] = i
    luaY:growvector(fs.L, f.lineinfo, fs.pc, f.sizelineinfo, nil, luaY.MAX_INT, "code size overflow")
    f.lineinfo[fs.pc] = line
    local pc = fs.pc
    fs.pc = fs.pc + 1
    return pc
end
function luaK:codeABC(fs, o, a, b, c)
    local i = {OP = luaP.OpCode[o], A = a, B = b, C = c}
    local f = fs.f
    luaK:dischargejpc(fs)
    luaY:growvector(fs.L, f.code, fs.pc, f.sizecode, nil, luaY.MAX_INT, "code size overflow")
    f.code[fs.pc] = i
    luaY:growvector(fs.L, f.lineinfo, fs.pc, f.sizelineinfo, nil, luaY.MAX_INT, "code size overflow")
    f.lineinfo[fs.pc] = fs.ls.lastline
    local pc = fs.pc
    fs.pc = fs.pc + 1
    return pc
end
function luaK:codeABx(fs, o, a, bc)
    return self:code(fs, luaP:CREATE_ABx(o, a, bc), fs.ls.lastline)
end
function luaK:setlist(fs, base, nelems, tostore)
    local c = math.floor((nelems - 1) / luaP.LFIELDS_PER_FLUSH) + 1
    local b = (tostore == luaY.LUA_MULTRET) and 0 or tostore
    if c <= luaP.MAXARG_C then
        self:codeABC(fs, "OP_SETLIST", base, b, c)
    else
        self:codeABC(fs, "OP_SETLIST", base, b, 0)
        self:code(fs, luaP:CREATE_Inst(c), fs.ls.lastline)
    end
    fs.freereg = base + 1
end
luaY.SHRT_MAX = 32767
luaY.LUAI_MAXVARS = 200
luaY.LUAI_MAXUPVALUES = 60
luaY.MAX_INT = luaK.MAX_INT or 2147483645
luaY.LUAI_MAXCCALLS = 200
luaY.VARARG_HASARG = 1
luaY.HASARG_MASK = 2
luaY.VARARG_ISVARARG = 2
luaY.VARARG_NEEDSARG = 4
luaY.LUA_MULTRET = -1
function luaY:LUA_QL(x)
    return "'" .. x .. "'"
end
function luaY:growvector(L, v, nelems, size, t, limit, e)
    if nelems >= limit then
        error(e)
    end
end
function luaY:newproto(L)
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
function luaY:int2fb(x)
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
function luaY:hasmultret(k)
    return k == "VCALL" or k == "VVARARG"
end
function luaY:getlocvar(fs, i)
    return fs.f.locvars[fs.actvar[i]]
end
function luaY:checklimit(fs, v, l, m)
    if v > l then
        self:errorlimit(fs, l, m)
    end
end
function luaY:anchor_token(ls)
    if ls.t.token == "TK_NAME" or ls.t.token == "TK_STRING" then
    end
end
function luaY:error_expected(ls, token)
    luaK:syntaxerror(ls, string.format("'%s' expected", luaK:token2str(ls, token)))
end
function luaY:errorlimit(fs, limit, what)
    local msg =
        (fs.f.linedefined == 0) and string.format("main function has more than %d %s", limit, what) or
        string.format("function at line %d has more than %d %s", fs.f.linedefined, limit, what)
    luaK:lexerror(fs.ls, msg, 0)
end
function luaY:testnext(ls, c)
    if ls.t.token == c then
        luaK:next(ls)
        return true
    else
        return false
    end
end
function luaY:check(ls, c)
    if ls.t.token ~= c then
        self:error_expected(ls, c)
    end
end
function luaY:checknext(ls, c)
    self:check(ls, c)
    luaK:next(ls)
end
function luaY:check_condition(ls, c, msg)
    if not c then
        luaK:syntaxerror(ls, msg)
    end
end
function luaY:check_match(ls, what, who, where)
    if not self:testnext(ls, what) then
        luaK:syntaxerror(
            ls,
            where == ls.linenumber and self.LUA_QS:format(luaK:token2str(ls, what)) .. " expected" or
                self.LUA_QS:format(luaK:token2str(ls, what)) ..
                    " expected (to close " .. self.LUA_QS:format(luaK:token2str(ls, who)) .. " at line %d)",
            where
        )
    end
end
function luaY:str_checkname(ls)
    self:check(ls, "TK_NAME")
    local ts = ls.t.seminfo
    luaK:next(ls)
    return ts
end
function luaY:init_exp(e, k, i)
    e.f, e.t = luaK.NO_JUMP, luaK.NO_JUMP
    e.k = k
    e.info = i
    e.nval = nil
    e.aux = nil
    return e
end
function luaY:codestring(ls, e, s)
    e.f, e.t = luaK.NO_JUMP, luaK.NO_JUMP
    e.k = "VK"
    e.info = luaK:stringK(ls.fs, s)
    e.nval = nil
    e.aux = nil
end
function luaY:checkname(ls, e)
    self:codestring(ls, e, self:str_checkname(ls))
end
function luaY:registerlocalvar(ls, varname)
    local fs = ls.fs
    local f = fs.f
    self:growvector(ls.L, f.locvars, fs.nlocvars, f.sizelocvars, nil, self.SHRT_MAX, "too many local variables")
    f.locvars[fs.nlocvars] = {}
    f.locvars[fs.nlocvars].varname = varname
    local nlocvars = fs.nlocvars
    fs.nlocvars = fs.nlocvars + 1
    return nlocvars
end
function luaY:new_localvarliteral(ls, v, n)
    self:new_localvar(ls, v, n)
end
function luaY:new_localvar(ls, name, n)
    local fs = ls.fs
    self:checklimit(fs, fs.nactvar + n + 1, self.LUAI_MAXVARS, "local variables")
    fs.actvar[fs.nactvar + n] = self:registerlocalvar(ls, name)
end
function luaY:adjustlocalvars(ls, nvars)
    local fs = ls.fs
    fs.nactvar = fs.nactvar + nvars
    for i = nvars, 1, -1 do
        self:getlocvar(fs, fs.nactvar - i).startpc = fs.pc
    end
end
function luaY:removevars(ls, tolevel)
    local fs = ls.fs
    while fs.nactvar > tolevel do
        fs.nactvar = fs.nactvar - 1
        self:getlocvar(fs, fs.nactvar).endpc = fs.pc
    end
end
function luaY:indexupvalue(fs, name, v)
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
function luaY:searchvar(fs, n)
    for i = fs.nactvar - 1, 0, -1 do
        if n == self:getlocvar(fs, i).varname then
            return i
        end
    end
    return -1
end
function luaY:markupval(fs, level)
    local bl = fs.bl
    while bl and bl.nactvar > level do
        bl = bl.previous
    end
    if bl then
        bl.upval = true
    end
end
function luaY:singlevaraux(fs, n, var, base)
    if fs == nil then
        self:init_exp(var, "VGLOBAL", luaP.NO_REG)
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
function luaY:singlevar(ls, var)
    local varname = self:str_checkname(ls)
    local fs = ls.fs
    if self:singlevaraux(fs, varname, var, 1) == "VGLOBAL" then
        var.info = luaK:stringK(fs, varname)
    end
end
function luaY:adjust_assign(ls, nvars, nexps, e)
    local fs, extra = ls.fs, nvars - nexps
    if self:hasmultret(e.k) then
        extra = extra + 1
        luaK:setreturns(fs, e, extra < 0 and 0 or extra)
        if extra > 1 then
            luaK:reserveregs(fs, extra - 1)
        end
    else
        if e.k ~= "VVOID" then
            luaK:exp2nextreg(fs, e)
        end
        if extra > 0 then
            luaK:_nil(fs, fs.freereg, extra)
            luaK:reserveregs(fs, extra)
        elseif nexps == 1 and nvars > 1 then
            local reg = fs.freereg - 1
            luaK:reserveregs(fs, nvars - 1)
            for i = 1, nvars - 1 do
                luaK:codeABC(fs, "OP_MOVE", reg + i, reg, 0)
            end
        end
    end
end
function luaY:enterlevel(ls)
    ls.L.nCcalls = ls.L.nCcalls + 1
    if ls.L.nCcalls > self.LUAI_MAXCCALLS then
        luaK:lexerror(ls, "chunk has too many syntax levels", 0)
    end
end
function luaY:leavelevel(ls)
    ls.L.nCcalls = ls.L.nCcalls - 1
end
function luaY:enterblock(fs, bl, isbreakable)
    bl.breaklist = luaK.NO_JUMP
    bl.continuelist = luaK.NO_JUMP
    bl.isbreakable = isbreakable
    bl.nactvar = fs.nactvar
    bl.upval = false
    bl.previous = fs.bl
    fs.bl = bl
end
function luaY:leaveblock(fs)
    local bl = fs.bl
    fs.bl = bl.previous
    self:removevars(fs.ls, bl.nactvar)
    if bl.upval then
        luaK:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
    end
    fs.freereg = fs.nactvar
    luaK:patchtohere(fs, bl.breaklist)
end
function luaY:pushclosure(ls, func, v)
    local fs = ls.fs
    local f = fs.f
    self:growvector(ls.L, f.p, fs.np, f.sizep, nil, luaP.MAXARG_Bx, "constant table overflow")
    f.p[fs.np] = func.f
    fs.np = fs.np + 1
    self:init_exp(v, "VRELOCABLE", luaK:codeABx(fs, "OP_CLOSURE", 0, fs.np - 1))
    for i = 0, func.f.nups - 1 do
        local o = (func.upvalues[i].k == "VLOCAL") and "OP_MOVE" or "OP_GETUPVAL"
        luaK:codeABC(fs, o, 0, func.upvalues[i].info, 0)
    end
end
function luaY:open_func(ls, fs)
    local L = ls.L
    local f = self:newproto(ls.L)
    fs.f = f
    fs.prev = ls.fs
    fs.ls = ls
    fs.L = L
    ls.fs = fs
    fs.pc = 0
    fs.lasttarget = -1
    fs.jpc = luaK.NO_JUMP
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
function luaY:close_func(ls)
    local L = ls.L
    local fs = ls.fs
    local f = fs.f
    self:removevars(ls, 0)
    luaK:ret(fs, 0, 0)
    for i = 0, fs.npendinggotos - 1 do
        local g = fs.pendinggotos[i]
        local target = self:searchlabel(fs, g.label)
        if target < 0 then
            luaK:syntaxerror(ls, string.format("label '%s' not found", g.label))
        end
        luaK:fixjump(fs, g.pc, target)
    end
    f.sizecode = fs.pc
    f.sizelineinfo = fs.pc
    f.sizek = fs.nk
    f.sizep = fs.np
    f.sizelocvars = fs.nlocvars
    f.sizeupvalues = f.nups
    ls.fs = fs.prev
    if fs then
        self:anchor_token(ls)
    end
end
function luaY:parser(L, z, buff, name)
    local lexstate = {t = {}, lookahead = {}}
    local funcstate = {upvalues = {}, actvar = {}}
    L.nCcalls = 0
    lexstate.buff = buff
    luaK:setinput(L, lexstate, z, name)
    luaY:open_func(lexstate, funcstate)
    funcstate.f.is_vararg = luaY.VARARG_ISVARARG
    luaK:next(lexstate)
    luaY:chunk(lexstate)
    luaY:checknext(lexstate, "TK_EOS")
    luaY:close_func(lexstate)
    return funcstate.f
end
function luaY:field(ls, v)
    local fs = ls.fs
    local key = {}
    luaK:exp2anyreg(fs, v)
    luaK:next(ls)
    self:checkname(ls, key)
    luaK:indexed(fs, v, key)
end
function luaY:yindex(ls, v)
    luaK:next(ls)
    self:expr(ls, v)
    luaK:exp2val(ls.fs, v)
    self:checknext(ls, "]")
end
function luaY:recfield(ls, cc)
    local fs = ls.fs
    local reg = ls.fs.freereg
    local key, val = {}, {}
    if ls.t.token == "TK_NAME" then
        self:checklimit(fs, cc.nh, self.MAX_INT, "items in a constructor")
        self:checkname(ls, key)
    else
        self:yindex(ls, key)
    end
    cc.nh = cc.nh + 1
    self:checknext(ls, "=")
    local rkkey = luaK:exp2RK(fs, key)
    self:expr(ls, val)
    luaK:codeABC(fs, "OP_SETTABLE", cc.t.info, rkkey, luaK:exp2RK(fs, val))
    fs.freereg = reg
end
function luaY:closelistfield(fs, cc)
    if cc.v.k == "VVOID" then
        return
    end
    luaK:exp2nextreg(fs, cc.v)
    cc.v.k = "VVOID"
    if cc.tostore == luaP.LFIELDS_PER_FLUSH then
        luaK:setlist(fs, cc.t.info, cc.na, cc.tostore)
        cc.tostore = 0
    end
end
function luaY:lastlistfield(fs, cc)
    if cc.tostore == 0 then
        return
    end
    if self:hasmultret(cc.v.k) then
        luaK:setmultret(fs, cc.v)
        luaK:setlist(fs, cc.t.info, cc.na, self.LUA_MULTRET)
        cc.na = cc.na - 1
    else
        if cc.v.k ~= "VVOID" then
            luaK:exp2nextreg(fs, cc.v)
        end
        luaK:setlist(fs, cc.t.info, cc.na, cc.tostore)
    end
end
function luaY:listfield(ls, cc)
    self:expr(ls, cc.v)
    self:checklimit(ls.fs, cc.na, self.MAX_INT, "items in a constructor")
    cc.na = cc.na + 1
    cc.tostore = cc.tostore + 1
end
function luaY:constructor(ls, t)
    local fs = ls.fs
    local line = ls.linenumber
    local pc = luaK:codeABC(fs, "OP_NEWTABLE", 0, 0, 0)
    local cc = {}
    cc.v = {}
    cc.na, cc.nh, cc.tostore = 0, 0, 0
    cc.t = t
    self:init_exp(t, "VRELOCABLE", pc)
    self:init_exp(cc.v, "VVOID", 0)
    luaK:exp2nextreg(ls.fs, t)
    self:checknext(ls, "{")
    repeat
        if ls.t.token == "}" then
            break
        end
        self:closelistfield(fs, cc)
        local c = ls.t.token
        if c == "TK_NAME" then
            luaK:lookahead(ls)
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
    luaP:SETARG_B(fs.f.code[pc], self:int2fb(cc.na))
    luaP:SETARG_C(fs.f.code[pc], self:int2fb(cc.nh))
end
function luaY:parlist(ls)
    local fs = ls.fs
    local f = fs.f
    local nparams = 0
    f.is_vararg = 0
    if ls.t.token ~= ")" then
        repeat
            local c = ls.t.token
            if c == "TK_NAME" then
                self:new_localvar(ls, self:str_checkname(ls), nparams)
                nparams = nparams + 1
            elseif c == "TK_DOTS" then
                luaK:next(ls)
                self:new_localvarliteral(ls, "arg", nparams)
                nparams = nparams + 1
                f.is_vararg = self.VARARG_HASARG + self.VARARG_NEEDSARG
                f.is_vararg = f.is_vararg + self.VARARG_ISVARARG
            else
                luaK:syntaxerror(ls, "<name> or " .. self:LUA_QL("...") .. " expected")
            end
        until f.is_vararg ~= 0 or not self:testnext(ls, ",")
    end
    self:adjustlocalvars(ls, nparams)
    f.numparams = fs.nactvar - (f.is_vararg % self.HASARG_MASK)
    luaK:reserveregs(fs, fs.nactvar)
end
function luaY:body(ls, e, needself, line)
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
    self:parlist(ls)
    self:checknext(ls, ")")
    self:chunk(ls)
    new_fs.f.lastlinedefined = ls.linenumber
    self:check_match(ls, "TK_END", "TK_FUNCTION", line)
    self:close_func(ls)
    self:pushclosure(ls, new_fs, e)
end
function luaY:explist1(ls, v)
    local n = 1
    self:expr(ls, v)
    while self:testnext(ls, ",") do
        luaK:exp2nextreg(ls.fs, v)
        self:expr(ls, v)
        n = n + 1
    end
    return n
end
function luaY:funcargs(ls, f)
    local fs = ls.fs
    local args = {}
    local nparams
    local line = ls.linenumber
    local c = ls.t.token
    if c == "(" then
        if line ~= ls.lastline then
            luaK:syntaxerror(ls, "ambiguous syntax (function call x new statement)")
        end
        luaK:next(ls)
        if ls.t.token == ")" then
            args.k = "VVOID"
        else
            self:explist1(ls, args)
            luaK:setmultret(fs, args)
        end
        self:check_match(ls, ")", "(", line)
    elseif c == "{" then
        self:constructor(ls, args)
    elseif c == "TK_STRING" then
        self:codestring(ls, args, ls.t.seminfo)
        luaK:next(ls)
    else
        luaK:syntaxerror(ls, "function arguments expected")
        return
    end
    local base = f.info
    if self:hasmultret(args.k) then
        nparams = self.LUA_MULTRET
    else
        if args.k ~= "VVOID" then
            luaK:exp2nextreg(fs, args)
        end
        nparams = fs.freereg - (base + 1)
    end
    self:init_exp(f, "VCALL", luaK:codeABC(fs, "OP_CALL", base, nparams + 1, 2))
    luaK:fixline(fs, line)
    fs.freereg = base + 1
end
function luaY:prefixexp(ls, v)
    local c = ls.t.token
    if c == "(" then
        local line = ls.linenumber
        luaK:next(ls)
        self:expr(ls, v)
        self:check_match(ls, ")", "(", line)
        luaK:dischargevars(ls.fs, v)
    elseif c == "TK_NAME" then
        self:singlevar(ls, v)
    else
        luaK:syntaxerror(ls, "unexpected symbol")
    end
    return
end
function luaY:primaryexp(ls, v)
    local fs = ls.fs
    local c = ls.t.token
    local line = ls.linenumber
    if c == "(" then
        luaK:next(ls)
        self:expr(ls, v)
        self:check_match(ls, ")", "(", line)
        luaK:dischargevars(fs, v)
    elseif c == "TK_NAME" then
        self:singlevar(ls, v)
    else
        luaK:syntaxerror(ls, string.format("unexpected symbol '%s'", luaK:token2str(ls, c)))
    end
    while true do
        c = ls.t.token
        if c == "." then
            self:field(ls, v)
        elseif c == "[" then
            local key = {}
            luaK:exp2anyreg(fs, v)
            self:yindex(ls, key)
            luaK:indexed(fs, v, key)
        elseif c == ":" then
            local key = {}
            luaK:next(ls)
            self:checkname(ls, key)
            luaK:_self(fs, v, key)
            self:funcargs(ls, v)
        elseif c == "TK_DOUBLECOLON" then
            luaK:next(ls)
        elseif c == "(" or c == "TK_STRING" or c == "{" then
            luaK:exp2nextreg(fs, v)
            self:funcargs(ls, v)
        else
            return
        end
    end
end
function luaY:gotostat(ls)
    local fs = ls.fs
    local label = self:str_checkname(ls)
    local g = self:searchlabel(fs, label)
    if g >= 0 then
        luaK:jump(fs, g)
    else
        self:addpendinggoto(fs, label)
    end
end
function luaY:labelstat(ls, label, line)
    local fs = ls.fs
    self:checkrepeated(fs, label)
    local g = luaK:getlabel(fs)
    self:addlabel(fs, label, g)
    self:checknext(ls, "TK_DOUBLECOLON")
end
function luaY:searchlabel(fs, label)
    for i = 0, fs.nlabels - 1 do
        if fs.labels[i].name == label then
            return fs.labels[i].pc
        end
    end
    return -1
end
function luaY:checkrepeated(fs, label)
    if self:searchlabel(fs, label) >= 0 then
        luaK:syntaxerror(fs.ls, string.format("label '%s' already defined", label))
    end
end
function luaY:addlabel(fs, label, pc)
    self:growvector(fs.L, fs.labels, fs.nlabels, fs.sizelabels, nil, self.MAX_INT, "too many labels")
    fs.labels[fs.nlabels] = {name = label, pc = pc}
    fs.nlabels = fs.nlabels + 1
end
function luaY:addpendinggoto(fs, label)
    self:growvector(
        fs.L,
        fs.pendinggotos,
        fs.npendinggotos,
        fs.sizependinggotos,
        nil,
        self.MAX_INT,
        "too many pending gotos"
    )
    fs.pendinggotos[fs.npendinggotos] = {label = label, pc = luaK:jump(fs)}
    fs.npendinggotos = fs.npendinggotos + 1
end
function luaY:simpleexp(ls, v)
    local c = ls.t.token
    if c == "TK_NUMBER" then
        v.f, v.t = luaK.NO_JUMP, luaK.NO_JUMP
        v.k = "VKNUM"
        v.info = 0
        v.nval = ls.t.seminfo
        v.aux = nil
    elseif c == "TK_STRING" then
        self:codestring(ls, v, ls.t.seminfo)
    elseif c == "TK_NIL" then
        v.f, v.t = luaK.NO_JUMP, luaK.NO_JUMP
        v.k = "VNIL"
        v.info = 0
        v.nval = nil
        v.aux = nil
    elseif c == "TK_TRUE" then
        v.f, v.t = luaK.NO_JUMP, luaK.NO_JUMP
        v.k = "VTRUE"
        v.info = 0
        v.nval = nil
        v.aux = nil
    elseif c == "TK_FALSE" then
        v.f, v.t = luaK.NO_JUMP, luaK.NO_JUMP
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
        v.f, v.t = luaK.NO_JUMP, luaK.NO_JUMP
        v.k = "VVARARG"
        v.info = luaK:codeABC(fs, "OP_VARARG", 0, 1, 0)
        v.nval = nil
        v.aux = nil
    elseif c == "{" then
        self:constructor(ls, v)
        return
    elseif c == "TK_FUNCTION" then
        luaK:next(ls)
        self:body(ls, v, false, ls.linenumber)
        return
    else
        self:primaryexp(ls, v)
        return
    end
    luaK:next(ls)
end
luaY.getbinopr_table = {
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
function luaY:getbinopr(op)
    local opr = self.getbinopr_table[op]
    if opr then
        return opr
    else
        return "OPR_NOBINOPR"
    end
end
function luaY:getunopr(token)
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
luaY.UNARY_PRIORITY = 8
function luaY:subexpr(ls, v, limit)
    luaY:enterlevel(ls)
    local token = ls.t.token
    local uop = self:getunopr(token)
    if uop ~= "OPR_NOUNOPR" then
        luaK:next(ls)
        luaY:subexpr(ls, v, luaY.UNARY_PRIORITY)
        luaK:prefix(ls.fs, uop, v)
    else
        luaY:simpleexp(ls, v)
    end
    local binop_info = luaY.getbinopr_table[ls.t.token]
    while binop_info and binop_info.left > limit do
        local op = binop_info.opr
        local v2 = {}
        luaK:next(ls)
        luaK:infix(ls.fs, op, v)
        local nextop_info = luaY:subexpr(ls, v2, binop_info.right)
        luaK:posfix(ls.fs, op, v, v2)
        binop_info = luaY.getbinopr_table[ls.t.token]
    end
    luaY:leavelevel(ls)
    return binop_info and binop_info.opr or "OPR_NOBINOPR"
end
function luaY:expr(ls, v)
    v = v or {f = luaK.NO_JUMP, t = luaK.NO_JUMP}
    if ls.t.token == "TK_IF" then
        self:ternary(ls, v)
    else
        self:subexpr(ls, v, 0)
    end
    return v
end
function luaY:block_follow(token)
    if token == "TK_ELSE" or token == "TK_ELSEIF" or token == "TK_END" or token == "TK_UNTIL" or token == "TK_EOS" then
        return true
    else
        return false
    end
end
function luaY:block(ls)
    local fs = ls.fs
    local bl = {}
    self:enterblock(fs, bl, false)
    self:chunk(ls)
    self:leaveblock(fs)
end
function luaY:check_conflict(ls, lh, v)
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
        luaK:codeABC(fs, "OP_MOVE", fs.freereg, v.info, 0)
        luaK:reserveregs(fs, 1)
    end
end
function luaY:assignment(ls, lh, nvars)
    local e = {}
    local c = lh.v.k
    self:check_condition(ls, c == "VLOCAL" or c == "VUPVAL" or c == "VGLOBAL" or c == "VINDEXED", "syntax error")
    if self:testnext(ls, "TK_DOUBLECOLON") then
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
        elseif ls.t.token == "=" then
            self:checknext(ls, "=")
            local nexps = self:explist1(ls, e)
            if nexps ~= nvars then
                self:adjust_assign(ls, nvars, nexps, e)
                if nexps > nvars then
                    ls.fs.freereg = ls.fs.freereg - (nexps - nvars)
                end
            else
                luaK:setoneret(ls.fs, e)
                luaK:storevar(ls.fs, lh.v, e)
                return
            end
        end
    elseif self:testnext(ls, ",") then
        local nv = {}
        nv.v = {}
        nv.prev = lh
        self:primaryexp(ls, nv.v)
        if nv.v.k == "VLOCAL" then
            self:check_conflict(ls, lh, nv.v)
        end
        self:checklimit(ls.fs, nvars, self.LUAI_MAXCCALLS - ls.L.nCcalls, "variables in assignment")
        self:assignment(ls, nv, nvars + 1)
    else
        local op = ls.t.token
        if
            op == "TK_ADD2" or op == "TK_SUB2" or op == "TK_MUL2" or op == "TK_DIV2" or op == "TK_MOD2" or
                op == "TK_POW2" or
                op == "TK_CONCAT2" or
                op == "TK_FLOORDIV2"
         then
            luaK:next(ls)
            local v = {}
            self:expr(ls, v)
            local binop = luaY:getbinopr(op)
            local var = {}
            var.k = lh.v.k
            var.info = lh.v.info
            var.aux = lh.v.aux
            luaK:posfix(ls.fs, binop, lh.v, v)
            luaK:storevar(ls.fs, var, lh.v)
        else
            self:checknext(ls, "=")
            local nexps = self:explist1(ls, e)
            if nexps ~= nvars then
                self:adjust_assign(ls, nvars, nexps, e)
                if nexps > nvars then
                    ls.fs.freereg = ls.fs.freereg - (nexps - nvars)
                end
            else
                luaK:setoneret(ls.fs, e)
                luaK:storevar(ls.fs, lh.v, e)
                return
            end
        end
    end
    self:init_exp(e, "VNONRELOC", ls.fs.freereg - 1)
    luaK:storevar(ls.fs, lh.v, e)
end
function luaY:cond(ls)
    local v = {}
    self:expr(ls, v)
    if v.k == "VNIL" then
        v.k = "VFALSE"
    end
    luaK:goiftrue(ls.fs, v)
    return v.f
end
function luaY:breakstat(ls)
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
        luaK:syntaxerror(ls, "no loop to break")
    end
    if upval then
        luaK:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
    end
    bl.breaklist = luaK:concat(fs, bl.breaklist, luaK:jump(fs))
end
function luaY:continuestat(ls)
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
        luaK:syntaxerror(ls, "no loop to continue")
    end
    if upval then
        luaK:codeABC(fs, "OP_CLOSE", bl.nactvar, 0, 0)
    end
    local jump = luaK:jump(fs)
    bl.continuelist = luaK:concat(fs, bl.continuelist, jump)
end
function luaY:whilestat(ls, line)
    local fs = ls.fs
    local bl = {}
    luaK:next(ls)
    local whileinit = luaK:getlabel(fs)
    local condexit = self:cond(ls)
    self:enterblock(fs, bl, true)
    self:checknext(ls, "TK_DO")
    self:block(ls)
    luaK:patchlist(fs, bl.continuelist, whileinit)
    luaK:patchlist(fs, luaK:jump(fs), whileinit)
    self:check_match(ls, "TK_END", "TK_WHILE", line)
    self:leaveblock(fs)
    luaK:patchtohere(fs, condexit)
end
function luaY:repeatstat(ls, line)
    local fs = ls.fs
    local repeat_init = luaK:getlabel(fs)
    local bl1, bl2 = {}, {}
    self:enterblock(fs, bl1, true)
    self:enterblock(fs, bl2, false)
    luaK:next(ls)
    self:chunk(ls)
    self:check_match(ls, "TK_UNTIL", "TK_REPEAT", line)
    local cond_start = fs.pc
    local condexit = self:cond(ls)
    if not bl2.upval then
        self:leaveblock(fs)
        luaK:patchlist(fs, bl1.continuelist, cond_start)
        luaK:patchlist(ls.fs, condexit, repeat_init)
    else
        self:breakstat(ls)
        luaK:patchlist(fs, bl1.continuelist, cond_start)
        luaK:patchtohere(ls.fs, condexit)
        self:leaveblock(fs)
        luaK:patchlist(ls.fs, luaK:jump(fs), repeat_init)
    end
    self:leaveblock(fs)
end
function luaY:exp1(ls)
    local e = {}
    self:expr(ls, e)
    local k = e.k
    luaK:exp2nextreg(ls.fs, e)
    return k
end
function luaY:forbody(ls, base, line, nvars, isnum)
    local bl = {}
    local fs = ls.fs
    self:adjustlocalvars(ls, 3)
    self:checknext(ls, "TK_DO")
    local prep =
        isnum and luaK:codeAsBx(fs, "OP_FORPREP", base, luaK.NO_JUMP) or luaK:jump(fs)
    self:enterblock(fs, bl, true)
    self:adjustlocalvars(ls, nvars)
    luaK:reserveregs(fs, nvars)
    self:block(ls)
    self:leaveblock(fs)
    local continue_target = fs.pc
    luaK:patchtohere(fs, bl.continuelist)
    luaK:patchtohere(fs, prep)
    local endfor =
        isnum and luaK:codeAsBx(fs, "OP_FORLOOP", base, luaK.NO_JUMP) or
        luaK:codeABC(fs, "OP_TFORLOOP", base, 0, nvars)
    luaK:fixline(fs, line)
    luaK:patchlist(fs, isnum and endfor or luaK:jump(fs), prep + 1)
end
function luaY:fornum(ls, varname, line)
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
        luaK:codeABx(fs, "OP_LOADK", fs.freereg, luaK:numberK(fs, 1))
        luaK:reserveregs(fs, 1)
    end
    self:forbody(ls, base, line, 1, true)
end
function luaY:forlist(ls, indexname)
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
    luaK:checkstack(fs, 3)
    self:forbody(ls, base, line, nvars - 3, false)
end
function luaY:forstat(ls, line)
    local fs = ls.fs
    local bl = {}
    self:enterblock(fs, bl, true)
    luaK:next(ls)
    local varname = self:str_checkname(ls)
    local c = ls.t.token
    if c == "=" then
        self:fornum(ls, varname, line)
    elseif c == "," or c == "TK_IN" then
        self:forlist(ls, varname)
    else
        luaK:syntaxerror(ls, self:LUA_QL("=") .. " or " .. self:LUA_QL("in") .. " expected")
    end
    self:check_match(ls, "TK_END", "TK_FOR", line)
    self:leaveblock(fs)
end
function luaY:test_then_block(ls)
    luaK:next(ls)
    local condexit = self:cond(ls)
    self:checknext(ls, "TK_THEN")
    self:block(ls)
    return condexit
end
function luaY:ifstat(ls, line)
    local fs = ls.fs
    local escapelist = luaK.NO_JUMP
    local flist = self:test_then_block(ls)
    while ls.t.token == "TK_ELSEIF" do
        escapelist = luaK:concat(fs, escapelist, luaK:jump(fs))
        luaK:patchtohere(fs, flist)
        flist = self:test_then_block(ls)
    end
    if ls.t.token == "TK_ELSE" then
        escapelist = luaK:concat(fs, escapelist, luaK:jump(fs))
        luaK:patchtohere(fs, flist)
        luaK:next(ls)
        self:block(ls)
    else
        escapelist = luaK:concat(fs, escapelist, flist)
    end
    luaK:patchtohere(fs, escapelist)
    self:check_match(ls, "TK_END", "TK_IF", line)
end
function luaY:localfunc(ls)
    local v, b = {}, {}
    local fs = ls.fs
    self:new_localvar(ls, self:str_checkname(ls), 0)
    self:init_exp(v, "VLOCAL", fs.freereg)
    luaK:reserveregs(fs, 1)
    self:adjustlocalvars(ls, 1)
    self:body(ls, b, false, ls.linenumber)
    luaK:storevar(fs, v, b)
    self:getlocvar(fs, fs.nactvar - 1).startpc = fs.pc
end
function luaY:ternary(ls, v)
    self:enterlevel(ls)
    local line = ls.linenumber
    luaK:next(ls)
    local cond = {}
    self:expr(ls, cond)
    luaK:goiftrue(ls.fs, cond)
    self:checknext(ls, "TK_THEN")
    local v_true = {}
    self:subexpr(ls, v_true, 0)
    luaK:exp2nextreg(ls.fs, v_true)
    local result_reg = v_true.info
    local jump_to_else = luaK:jump(ls.fs)
    luaK:patchtohere(ls.fs, cond.f)
    local v_false = {}
    while ls.t.token == "TK_ELSEIF" do
        luaK:next(ls)
        local elseif_cond = {}
        self:expr(ls, elseif_cond)
        luaK:goiftrue(ls.fs, elseif_cond)
        self:checknext(ls, "TK_THEN")
        local elseif_val = {}
        self:subexpr(ls, elseif_val, 0)
        luaK:exp2nextreg(ls.fs, elseif_val)
        local elseif_reg = elseif_val.info
        if elseif_reg ~= result_reg then
            luaK:codeABC(ls.fs, "OP_MOVE", result_reg, elseif_reg, 0)
            luaK:freereg(ls.fs, elseif_reg)
        end
        jump_to_else = luaK:concat(ls.fs, jump_to_else, luaK:jump(ls.fs))
        luaK:patchtohere(ls.fs, elseif_cond.f)
    end
    self:checknext(ls, "TK_ELSE")
    self:subexpr(ls, v_false, 0)
    luaK:exp2nextreg(ls.fs, v_false)
    local false_reg = v_false.info
    if false_reg ~= result_reg then
        luaK:codeABC(ls.fs, "OP_MOVE", result_reg, false_reg, 0)
        luaK:freereg(ls.fs, false_reg)
    end
    local end_jump = luaK:jump(ls.fs)
    luaK:patchtohere(ls.fs, jump_to_else)
    self:init_exp(v, "VNONRELOC", result_reg)
    v.t = luaK.NO_JUMP
    v.f = luaK.NO_JUMP
    luaK:patchtohere(ls.fs, end_jump)
    self:leavelevel(ls)
end
function luaY:localstat(ls)
    local nvars = 0
    local nexps
    local e = {}
    repeat
        local varname = self:str_checkname(ls)
        self:new_localvar(ls, varname, nvars)
        nvars = nvars + 1
    until not self:testnext(ls, ",")
    if self:testnext(ls, "=") then
        nexps = self:explist1(ls, e)
    else
        e.k = "VVOID"
        nexps = 0
    end
    self:adjust_assign(ls, nvars, nexps, e)
    self:adjustlocalvars(ls, nvars)
end
function luaY:funcname(ls, v)
    local needself = false
    self:singlevar(ls, v)
    while ls.t.token == "." do
        self:field(ls, v)
    end
    if ls.t.token == ":" then
        needself = true
        self:field(ls, v)
    end
    return needself
end
function luaY:funcstat(ls, line)
    local v, b = {}, {}
    luaK:next(ls)
    local needself = self:funcname(ls, v)
    self:body(ls, b, needself, line)
    luaK:storevar(ls.fs, v, b)
    luaK:fixline(ls.fs, line)
end
function luaY:exprstat(ls)
    local fs = ls.fs
    local v = {}
    v.v = {}
    self:primaryexp(ls, v.v)
    if v.v.k == "VCALL" then
        luaP:SETARG_C(luaK:getcode(fs, v.v), 1)
    else
        v.prev = nil
        self:assignment(ls, v, 1)
    end
end
function luaY:retstat(ls)
    local fs = ls.fs
    local e = {}
    local first, nret
    luaK:next(ls)
    if self:block_follow(ls.t.token) or ls.t.token == ";" then
        first, nret = 0, 0
    else
        nret = self:explist1(ls, e)
        if self:hasmultret(e.k) then
            luaK:setmultret(fs, e)
            if e.k == "VCALL" and nret == 1 then
                luaP:SET_OPCODE(luaK:getcode(fs, e), "OP_TAILCALL")
            end
            first = fs.nactvar
            nret = self.LUA_MULTRET
        else
            if nret == 1 then
                first = luaK:exp2anyreg(fs, e)
            else
                luaK:exp2nextreg(fs, e)
                first = fs.nactvar
            end
        end
    end
    luaK:ret(fs, first, nret)
end
local statement_handlers = {
    TK_IF = luaY.ifstat,
    TK_WHILE = luaY.whilestat,
    TK_DO = function(self, ls, line)
        luaK:next(ls)
        self:block(ls)
        self:check_match(ls, "TK_END", "TK_DO", line)
        return false
    end,
    TK_FOR = luaY.forstat,
    TK_REPEAT = luaY.repeatstat,
    TK_FUNCTION = luaY.funcstat,
    TK_LOCAL = function(self, ls)
        luaK:next(ls)
        if self:testnext(ls, "TK_FUNCTION") then
            self:localfunc(ls)
        else
            self:localstat(ls)
        end
        return false
    end,
    TK_RETURN = luaY.retstat,
    TK_BREAK = function(self, ls)
        luaK:next(ls)
        self:breakstat(ls)
        return true
    end,
    TK_CONTINUE = function(self, ls)
        luaK:next(ls)
        self:continuestat(ls)
        return true
    end,
    TK_GOTO = function(self, ls)
        luaK:next(ls)
        self:gotostat(ls)
        return true
    end,
    TK_DOUBLECOLON = function(self, ls)
        luaK:next(ls)
        self:labelstat(ls, self:str_checkname(ls), ls.linenumber)
        return false
    end
}
function luaY:statement(ls)
    local line = ls.linenumber
    local token = ls.t.token
    local handler = statement_handlers[token]
    if handler then
        return handler(self, ls, line)
    else
        self:exprstat(ls)
        return false
    end
end
function luaY:chunk(ls)
    local islast = false
    luaY:enterlevel(ls)
    while not islast and not luaY:block_follow(ls.t.token) do
        islast = luaY:statement(ls)
        if ls.t.token == ";" then
            luaK:next(ls)
        end
        ls.fs.freereg = ls.fs.nactvar
    end
    luaY:leavelevel(ls)
end
local opnames = {
    [0] = "MOVE",
    [1] = "LOADK",
    [2] = "LOADBOOL",
    [3] = "LOADNIL",
    [4] = "GETUPVAL",
    [5] = "GETGLOBAL",
    [6] = "GETTABLE",
    [7] = "SETGLOBAL",
    [8] = "SETUPVAL",
    [9] = "SETTABLE",
    [10] = "NEWTABLE",
    [11] = "SELF",
    [12] = "ADD",
    [13] = "SUB",
    [14] = "MUL",
    [15] = "DIV",
    [16] = "MOD",
    [17] = "POW",
    [18] = "UNM",
    [19] = "NOT",
    [20] = "LEN",
    [21] = "CONCAT",
    [22] = "JMP",
    [23] = "EQ",
    [24] = "LT",
    [25] = "LE",
    [26] = "TEST",
    [27] = "TESTSET",
    [28] = "CALL",
    [29] = "TAILCALL",
    [30] = "RETURN",
    [31] = "FORLOOP",
    [32] = "FORPREP",
    [33] = "TFORLOOP",
    [34] = "SETLIST",
    [35] = "CLOSE",
    [36] = "CLOSURE",
    [37] = "VARARG"
}
local function constToString(k)
    if type(k.value) == "string" then
        return '"' .. k.value .. '"'
    else
        return tostring(k.value)
    end
end
local function printFuncHeader(func, addr)
    local nconst = func.sizek or #func.k
    local nloc = func.sizelocvars or #(func.locvars or {})
    local nups = func.sizeupvalues or #(func.upvalues or {})
    local nsubs = func.sizep or #(func.p or {})
    local line1 = func.lineDefined or 0
    local line2 = func.lastlinedefined or 0
    local inscount = func.sizecode or #(func.code or {})
    local size_in_bytes = inscount * 4
    print(
        string.format(
            "main <%s:%d,%d> (%d instructions, %d bytes at %s)",
            func.source or "?",
            line1,
            line2,
            inscount,
            size_in_bytes,
            tostring(addr)
        )
    )
    print(
        string.format(
            "%d%s params, %d slots, %d upvalues, %d local, %d constant, %d function",
            func.numparams or 0,
            (func.is_vararg and "+" or ""),
            func.maxstacksize or 0,
            nups,
            nloc,
            nconst,
            nsubs
        )
    )
end
local function printInstruction(pc, instr, line, k)
    local op = opnames[instr.OP or 0] or ("<OP " .. tostring(instr.OP) .. ">")
    local a, b, c, bx = instr.A or 0, instr.B or 0, instr.C or 0, instr.Bx
    local sBx = instr.sBx
    io.write(string.format("\t%-4d  [%d]  %-10s", pc, line or 0, op))
    if bx ~= nil then
        io.write(string.format("\t%d %d", a, bx))
        if op == "LOADK" and k and k[bx] then
            io.write("\t; ", constToString(k[bx]))
        end
    elseif op == "JMP" and sBx then
        io.write(string.format("\t%d", sBx))
    elseif op == "SETLIST" then
        io.write(string.format("\t%d %d %d", a, b, c))
    else
        io.write(string.format("\t%d %d %d", a, b, c))
        if (op == "LOADK" or op == "GETGLOBAL" or op == "SETGLOBAL") and k and b and k[b] then
            io.write("\t; ", constToString(k[b]))
        end
    end
    io.write("\n")
end
local function printProto(func, addr)
    printFuncHeader(func, addr or tostring(func))
    for i = 1, func.sizecode or #func.code do
        local instr = func.code[i - 1]
        if instr then
            local line = func.lineinfo and func.lineinfo[i - 1] or 0
            printInstruction(i, instr, line, func.k)
        end
    end
    print("")
    if func.p then
        for i = 1, func.sizep or #func.p do
            local sub = func.p[i - 1]
            if sub then
                printProto(sub, tostring(sub))
            end
        end
    end
end
luaK:init()
local LuaState = {}
function compile(source, name, list_only)
    name = name or "compiled-lua"
    local zio = luaZ:init(luaZ:make_getF(source), nil)
    if not zio then
        error("Failed to initialize input buffer")
    end
    local LuaState = {}
    local func = luaY:parser(LuaState, zio, nil, "@" .. name)
    if list_only then
        printProto(func)
        return
    end
    local writer, buff = luaU:make_setS()
    local status = luaU:dump(LuaState, func, writer, buff)
    if status ~= 0 then
        error("Failed to serialize bytecode")
    end
    return buff.data
end
return compile

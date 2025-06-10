<pre align="center">
$$$$$$$$\                              $$\                               
\____$$  |                             \__|                              
    $$  /$$\   $$\  $$$$$$\  $$\   $$\ $$\  $$$$$$\  $$$$$$$\   $$$$$$\  
   $$  / $$ |  $$ |$$  __$$\ \$$\ $$  |$$ | \____$$\ $$  __$$\ $$  __$$\ 
  $$  /  $$ |  $$ |$$$$$$$$ | \$$$$  / $$ | $$$$$$$ |$$ |  $$ |$$ /  $$ |
 $$  /   $$ |  $$ |$$   ____| $$  $$<  $$ |$$  __$$ |$$ |  $$ |$$ |  $$ |
$$$$$$$$\\$$$$$$  |\$$$$$$$\ $$  /\$$\ $$ |\$$$$$$$ |$$ |  $$ |\$$$$$$$ |
\________|\______/  \_______|\__/  \__|\__| \_______|\__|  \__| \____$$ |
                                                               $$\   $$ |
                                                               \$$$$$$  |
                                                                \______/ 
</pre>

<p align="center">
  <img src="https://img.shields.io/github/stars/MarchHubOnTopFr/Zuexiang?style=flat-square" alt="Stars" />
  <img src="https://img.shields.io/github/forks/MarchHubOnTopFr/Zuexiang?style=flat-square" alt="Forks" />
  <img src="https://img.shields.io/github/issues/MarchHubOnTopFr/Zuexiang?style=flat-square" alt="Issues" />
  <img src="https://img.shields.io/github/license/MarchHubOnTopFr/Zuexiang?style=flat-square" alt="License" />
  <img src="https://img.shields.io/github/last-commit/MarchHubOnTopFr/Zuexiang?style=flat-square" alt="Last Commit" />
</p>

---

### ⚡ Zuexiang (ZX / ZueX / YueliangX)

**Zuexiang** is a personal fork of [Yueliang](http://yueliang.luaforge.net/), a Lua 5.1 bytecode compiler.  

This is not a production-grade compiler — more like a fun playground that sometimes works well and sometimes explodes.  
Still, it's fast, and the syntax extensions can be useful if you're into that.

---

### ✨ Features (Added or Tweaked)

- `continue` support
- `goto` + labels
- Compound assignment (`+=`, `-=`, etc.)
- `!=` as alias for `~=`
- Luau-style number literals (`1e3`, `0xFF`, etc.)
- Ternary expressions in `local` declarations
- Integer division operator (`//`)
- Still outputs standard Lua 5.1 bytecode
- Performance is decent

### ⚠️ Known Limitations

- Comments are stripped (not supported in parsing stage)
- The codebase is messy — I wrote most of it in bursts
- Not very optimized (instruction count and compiler size)
- Some identifiers are just `x`, `f`, etc. — sorry, I got lazy

In short: it runs, it compiles, but don’t expect clean architecture.

🧾 License

Zuexiang is released under the MIT License — do whatever you want with it.
Original base: Yueliang, also MIT.

👾 About

Made by Nyreel
Alias: ZueX, ZX, YueliangX

> Built fast, not clean. Shared just in case someone finds it useful.

If you find this project helpful or interesting, a ⭐ is always appreciated.

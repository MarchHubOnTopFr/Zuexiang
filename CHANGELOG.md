# Changelog

## [v1.1] - 2025-06-08

### Added
- Type annotation, type assertion, and type definition parsing
- Parsing support for `<const>` and `<close>` qualifiers
- Binary, octal, and underscored numeric literal support
- New readable names for compiler scripts (`luak`, `luac`, etc.)

### Fixed
- Compound assignment now properly handles table/indexed expressions (e.g., `pos.x += 1`)
- Goto edge case issues related to label jumps and variable scope

### Improved
- Optimized parsing performance (~0.28s compile time)
- Cleanup and minor refactors for internal clarity

---

## [v1.0] - Initial Release

- Forked from Yueliang Lua 5.1 compiler
- Added support for:
  - `goto` + labels
  - `continue`
  - Compound assignment (`+=`, `-=`, etc.)
  - `!=` alias
  - Luau-style number literals
  - Ternary expressions
  - Integer division (`//`)

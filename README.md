# Funk Programming Language

A functional programming language with trait-based polymorphism and dictionary-passing compilation to Core IR.

## Package Structure

This project is organized with three packages in the `packages/` directory:

### `packages/funk-core`
Core types and data structures shared across the toolchain:
- `Funk.Term` - Surface language AST
- `Funk.Token` - Lexical tokens
- `Funk.STerm` - Elaborated terms with explicit types
- `Funk.Fresh` - Fresh variable generation
- `Funk.Core` - Core IR representation

### `packages/funkc` 
The Funk compiler that transforms source code to Core IR:
- `Funk.Parser` - Parser for Funk syntax
- `Funk.Infer` - Type inference engine
- `Funk.Solver` - Constraint solver
- `Funk.KindInfer` - Kind inference
- `Funk.Compiler` - Main compilation pipeline
- `Funk.Dictionary` - Dictionary-based trait resolution
- `Funk.Subst` - Type substitution
- `Funk.Fmt` - Code formatter
- `Funk` - CLI interface

**Executable:** `funkc` - Compiles Funk programs to `.funkc` Core IR files

### `packages/funkvm`
Virtual machine for interpreting compiled Core IR:
- `Funk.Interpreter` - Core IR interpreter (placeholder)

**Executable:** `funkvm` - Runs compiled `.funkc` files

## Building

```bash
# Build all packages
cabal build all

# Build individual packages
cabal build funk-core
cabal build funkc
cabal build funkvm
```

## Usage

### Compiling Programs
```bash
# Compile with default target directory (./target/)
cabal run funkc -- build examples/main.funk --lib examples/lib/

# Compile with custom target directory
cabal run funkc -- build examples/main.funk --lib examples/lib/ --target build-output

# Format code
cabal run funkc -- fmt examples/
```

### Running Programs
```bash
# Run the virtual machine (placeholder)
cabal run funkvm
```

## Output

The compiler generates Core IR files with:
- **Explicit type annotations**: `let id : forall a . a -> a = \x:_. x`
- **Dictionary-based trait resolution**: `(Functor@_ { }).fmap f fa`
- **Nested directory structure**: `Control/Monad.funkc`, `Data/Bool.funkc`
- **Clean compilation output**: Only shows "Wrote {path}" for successful builds

## Architecture

The compilation pipeline:
1. **Parse** surface syntax to AST (`Funk.Parser`)
2. **Type inference** with constraint generation (`Funk.Infer`)
3. **Constraint solving** for trait resolution (`Funk.Solver`)
4. **Dictionary compilation** for trait methods (`Funk.Dictionary`)
5. **Core IR generation** with explicit types (`Funk.Compiler`)
6. **File output** to nested `.funkc` files (`Funk`)

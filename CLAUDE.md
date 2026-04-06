# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

A Lean 4 educational game teaching abstract algebra (group theory, ring theory, Galois theory) built on the [lean4game](https://github.com/leanprover-community/lean4game) framework. Targeted at MAT211/MAT205 students at Xiamen University Malaysia.

## Build Commands

```bash
# Install Lean toolchain (via elan)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Fetch mathlib cache (critical - avoids rebuilding mathlib from source)
lake exe cache get

# Build the game
lake build

# Build with local GameServer (requires ../lean4game/server/)
lake update -Klean4game.local

# Reset to remote GameServer
lake update -R
```

Lean toolchain version is pinned in `lean-toolchain` (currently v4.23.0). The `lakefile.lean` requires mathlib at the matching version tag.

## Architecture

- **`Game.lean`** - Main entry point. Imports worlds and calls `MakeGame`. Worlds are enabled/disabled by commenting imports here.
- **`Game/Metadata.lean`** - Shared imports (GameServer, Mathlib.Tactic, Mathlib.Data.Set.Basic) available to all levels.
- **`lakefile.lean`** - Toggles between local and remote GameServer via `-Klean4game.local` flag. Disables all linters and sets `tactic.hygienic` to false (important for gameplay).

### Level File Structure

Each level file follows this pattern:
```lean
import Game.Metadata

World "WorldName"
Level N

Title "..."
Introduction "..."

Statement ... := by
  Hint "..."
  Branch    -- alternative solution paths
    ...
  ...

Conclusion "..."
NewTactic tactic1 tactic2
NewTheorem thm1
NewDefinition def1
```

- **Worlds** are directories under `Game/Levels/` (e.g., `BasicLean/`, `BasicGroupTheory/`).
- Each world has an aggregator file (e.g., `BasicLean.lean`) that imports all its `L01_*.lean` through `LNN_*.lean` files.
- Levels within a world must be imported in order (bug in framework).
- `sofi.py` is a utility for renumbering/reordering level files within a world.

### Key Directories

- `Game/Levels/Lemmas/` - Shared auxiliary lemmas (group theory, partitions, computable ZMod/Order).
- `Game/Generator/` - LLM integration (API.lean, Basic.lean) for automated hint generation via multiple providers.
- `Game/Playground/` - Experimental/scratch files, not imported by the game.

## CI/CD

Two GitHub Actions workflows in `.github/workflows/`:
- **`build.yml`** - Runs on `main` push. Builds game + gameserver, creates `game.zip` artifact for deployment to `adam.math.hhu.de`.
- **`build_non_main.yml`** - Runs on non-main branch pushes. Only validates `lake build` succeeds (no artifact).

Both install elan v3.0.0, fetch mathlib cache, then build.

## Important Notes

- The `package Game` config in `lakefile.lean` disables `linter.all` and sets `tactic.hygienic` to false -- these are intentional for the game player experience, not mistakes.
- `lake exe cache get` fetches prebuilt mathlib `.olean` files. Without this, builds take hours.
- The mathlib version must match the Lean toolchain version (both use `leanVersion` in lakefile).

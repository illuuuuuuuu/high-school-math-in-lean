# High School Mathematics in Lean

A Lean 4 library for formally verified elementary mathematics.

## Author

Illusix Liu

## Goals

- express mathematical statements with explicit types and assumptions;
- reuse standard definitions and results from Mathlib;
- provide complete proofs checked by the Lean kernel;
- organize material as a conventional Lean library;
- keep every verified declaration free of `sorry` and unsupported axioms.

## Current contents

The library currently contains 373 verified Lean declarations covering logic and set theory, algebra, functions, trigonometry, plane vectors, sequences, complex numbers, solid geometry, statistics, and probability.

A further 35 foundational statements are represented directly by Lean or Mathlib primitives, giving a total coverage of 408 elementary mathematical statements.

## Build

Install Lean through `elan`, then run:

```bash
lake update
lake build
```

The Lean and Mathlib revisions are pinned by `lean-toolchain` and `lakefile.toml`.

## Repository contents

This repository contains original Lean source code and project documentation. No external textbook, source manuscript, image collection, or typesetting project is included.

## Copyright

Copyright © 2026 Illusix Liu. All rights reserved. See [COPYRIGHT.md](COPYRIGHT.md).

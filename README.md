# Idris2-Multiset-Transform

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 2 Universal Multiset Transform Engine & Logarithmic MultisetTree Data Structures**

`Idris2-Multiset-Transform` implements $O(\log N)$ parallelized multiset transformations and spatial state representations for the constructive physics pipeline:

- **`UnixelFraction`**: Exact rational fractions $(p/q)$ with `rationalEquivBit` cross-multiplication equivalence and compile-time `%macro auditUnixelFraction`.
- **`MultisetTree`**: Balanced binary multiset trees providing $O(\log N)$ lookup, insertion, and sum preservation over linear lists.
- **`Vexel` / `Maxel` / `Boxel`**: 1D, 2D, and 3D multiset basis tensors (Wildberger vectors, matrices, and volumes).
- **Fast Exponentiation**: Structural fuel-bounded $O(\log k)$ binary exponentiation (`fastNatPower2`).

## 🚀 Building & Installing

```bash
idris2 --build Idris2-Multiset-Transform.ipkg
idris2 --install Idris2-Multiset-Transform.ipkg
```

## 🔬 Architectural Features

- **Compile-Time Invariant Reflection**: Macro reflection proof tactics (`%macro`) verifying rational equivalence and tree properties at compile time.
- **Quantitative Type Theory**: Enforces linear multiplicity `(1 state : UniverseState vm de dm)` preventing state leakage.

# Idris2-Multiset-Transform

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 2 Exact Rational Fields, Goh Polynomial Factorizations & 5-Stage Scale Category Engine for Idris 2**

`Idris2-Multiset-Transform` forms the primary engine of **Layer 2** in the 10-layer constructive non-linear multiset science framework. It provides exact rational arithmetic (`UnixelFraction`), 1D Vexels & 2D Maxel matrices (`VexelMaxel`), monomorphic integer box matrix multiplication (`multBoxMatrix2D`), Goh spread polynomial factorizations (`GohMultiset`), $O(\log N)$ parallelized multiset trees (`MultisetTree`), and the formal 5-stage scale category (`ScaleCategory` & `ScalePipeline`).

---

## 📦 Core Library Architecture & Modules

### 1. `Core.UnixelFraction`
- **Exact Rational Fields:** Infinite-precision rational numbers (`UnixelFraction = Over num den`) replacing double-precision floating-point approximations.
- **Zero-Defect Arithmetic:** Primitive operations (`add`, `sub`, `mult`, `div`) and Diophantine cross-multiplication comparison functions eliminating continuous drift.
- **Macro Reflection:** Compile-time reflection auditor (`%macro auditUnixelFraction`) verifying rational identity invariants.

### 2. `Core.VexelMaxel`
- **Multiset Vector/Matrix Tensors:** 1D `Vexel` vectors and 2D `Maxel` transformation matrices over basis states.
- **$\beta$-Redex Contraction:** `actMaxelVexel` matrix-vector application, representing $\beta$-reduction as particle transformation.
- **Monomorphic Matrix Arithmetic:** `multBoxMatrix2D` and `traceBoxMatrix2D` integer matrix operations bypassing typeclass method blocking during elaborator evaluation.

### 3. `Core.ScaleCategory` & `Core.ScalePipeline`
- **Formal Scale Category:** Physical scale levels (`ScaleLevel`: SubatomicLevel, HadronLevel, AtomLevel, MoleculeLevel, CellLevel) and functorial scale wrappers (`ScaleFunctor`).
- **Functorial Composition:** Associative composition of scale functors (`composeScaleFunctors`) establishing scale-invariant mappings across physical domains.
- **5-Stage Scale Pipeline:** Unified scale pipeline (`sf1_QuarkToHadron` .. `sfTotalFunctorialPipeline`) formalizing physical ascent from subatomic color charges to complex biological modules.

### 4. `Core.Goh` & `Math.Transform.Reflect.Goh`
- **Wildberger Spread Polynumbers:** Goh auxiliary polynomial factorization ($\Phi_d(s)$) over rational spread polynomials.
- **Factor Multiset Trees:** `GohMultiset` trees storing factorized spread polynomials, evaluating wave propagation and multi-turn particle evolutions via exact polynomial multiplication.

### 5. `Core.MultisetTree`
- **Logarithmic State Data Structures:** Balanced binary multiset trees (`MultisetTree`) providing $O(\log N)$ parallelized lookup, insertion, and sum preservation over linear lists.
- **Fast Binary Exponentiation:** Structural fuel-bounded $O(\log k)$ binary exponentiation (`fastNatPower2`).

### 6. `Core.MaxelTransform`
- **Pushforward & Pullback Operators:** Transform multisets (`TransformMultiset`), forward contraction ($f_*$), and reverse-causal pullback expansion ($f^*$).

### 7. `Core.UniverseState`, `Core.LinearBuffer` & `Math.LawAlgebra`
- **QTT Simulation State:** Linear simulation containers (`UniverseState`) enforcing linear state preservation (multiplicity 1).
- **Physical Law Algebras:** Open stateful law interfaces (`StatefulLaw`), law action functions, and physical law combination monoids.

---

## 🚀 Building & Installing

```bash
idris2 --build Idris2-Multiset-Transform.ipkg
idris2 --install Idris2-Multiset-Transform.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all transformation modules.
- **Zero Floating-Point Drift:** Exact rational (`UnixelFraction`) arithmetic eliminating numerical rounding defects.
- **Functorial Scale Categories:** Structure-preserving `ScaleFunctor` pipelines mapping micro-states to macro-envelopes.
- **Elaborator Efficiency:** Monomorphic box matrix operations preventing typeclass method blocking during compile-time `%macro` reflection.

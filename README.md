# 🌀 Idris2-Multiset1

**Multiset 2-Category, Transform Monoids & Quantum Density Matrices for Idris 2**

`Idris2-Multiset1` builds upon `Idris2-Multiset0` to implement categorical state dynamics:
- `TransformMultiset`: 1-cell law transforms ($T: a \to b$) mapping multiset state configurations across metric sectors.
- **Lie Bracket Commutators**: $[T_1, T_2] = (T_1 \circ T_2) \ominus (T_2 \circ T_1)$ using exact multiset subtraction `subBox`.
- **Quantum Density Matrices**: Positive semi-definite operator multisets $\rho$ with exact trace normalization ($\text{Tr}(\rho) = 1$) and partial trace extraction.
- **Hyper-Tensors**: Multidimensional discrete contraction networks.

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`):

```bash
idris2 --build Idris2-Multiset1.ipkg
idris2 --install Idris2-Multiset1.ipkg
```

---

## 🔬 Language & Framework Integration

Written in **Idris 2** enforcing total constructivism (`%default total`).

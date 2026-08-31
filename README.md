# 🗃️ Idris2-Multiset2

**Next-Generation Constructive Multiset Data Structures in [Idris 2](https://github.com/idris-lang/Idris2): $O(\log N)$ Multiset Search Trees, Reflected Polynumbers, SingFractions, and Galois Law Algebra.**

[![Idris2](https://img.shields.io/badge/Idris2-Multiset2-blue.svg)](https://github.com/idris-lang/Idris2)

---

## 🏛️ Overview

`Idris2-Multiset2` extracts and modularizes the high-performance multiset structures from [`Idris2-Universe2`](../Idris2-Universe2), creating a standalone Layer 1 data structure library.

### Core Modules

1. **`Core.MultisetTree`**: Balanced Binary Search Trees providing $O(\log N)$ token insertion, lookup, and multiplicity preservation.
2. **`Core.Polynumber`**: Reflected Polynumber multisets, Goh Factorization, Cyclotomic Division ($\Phi_{137}$), and Spread Polynumbers $S_n(s)$.
3. **`Core.UnixelFraction`**: `SingFraction` / rational Hehner chance fractions with exact cross-multiplication equivalence (`rationalEquiv f1 f2`).
4. **`Core.VexelMaxel`**: Tensor multiset hierarchy: `Unixel` [n], `Pixel` [i,j], `Voxel` [x,y,z], `Vexel` (1D), `Maxel` (2D), `Boxel` (3D), and `HyperBoxel` (4D).
5. **`Math.LawAlgebra`**: Typed Law Algebra Monoid ($\wedge, \otimes$), multiset pushforward ($f_*$), inverse image pullback ($f^*$), and Galois Connections ($f_* \dashv f^*$).

---

## 🛠️ Building & Installing

```bash
toolbox run -c fedora-toolbox-44 /var/home/justin/.local/bin/idris2 --build Idris2-Multiset2.ipkg
toolbox run -c fedora-toolbox-44 /var/home/justin/.local/bin/idris2 --install Idris2-Multiset2.ipkg
```

---

© Justin Kelly. All rights reserved.

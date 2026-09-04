# 🌀 Idris2-Multiset-Transform

**Multiset Maxel Algebra, Unixel Fractions, $O(\log N)$ MultisetTrees & Discrete State Dynamics for Idris 2**

`Idris2-Multiset-Transform` builds upon `Idris2-Multiset-Core` to implement discrete multiset **Maxel** algebra, exact rational **UnixelFractions**, $O(\log N)$ **MultisetTrees**, and linear state transformations. In accordance with Norman Wildberger's finitist physics, continuous/rigid matrices are replaced by **Maxels** (multisets of coordinate pixels) and **Vexels** (multisets of vector singletons):

- **Maxel Transforms (`MaxelTransform`)**: Weighted multiset pixel tables $[((x, y), w)]$ mapping input Vexel densities to output Vexel densities across metric sectors.
- **Pushforward & Pullback Operators**:
  - **Pushforward (`pushforward` / `applyPushforward`)**: Forward maxel application multiplying input vexel counts by pixel weights: $(f_* M)(y) = \sum_x M(x) \cdot T(x, y)$.
  - **Pullback (`pullback` / `applyPullback`)**: Transpose maxel application pulling target counts back to source keys: $(f^* N)(x) = \sum_y N(y) \cdot T(x, y)$.
- **Maxel Commutators (`maxelCommutator` / `commutatorMaxels`)**: $[T_1, T_2] = (T_1 \circ T_2) \ominus (T_2 \circ T_1)$ measuring directional maxel application order differences via exact multiset difference `subBox`.
- **Exact Rational Observable (`UnixelFraction`)**: Exact rational fraction $Q = N / [D]$ with signed BoxInt numerator and non-zero positive Unixel denominator. Supports continued fractions, Stern-Brocot rational paths, and Hehner scale conversions.
- **Fast Multiset Trees (`MultisetTree`)**: $O(\log N)$ balanced search trees supporting parallel divide-and-conquer tree pushforward contractions (`applyPushforwardParallel`).
- **Polynumber Caret Algebra (`Polynumber`)**: Caret operation products and Fundamental Identity of Arithmetic (FIA) Euler product factorizations.

---

## 🔀 Maxel Algebra $\longleftrightarrow$ Matrix Terminology $\longleftrightarrow$ Category Theory

| Maxel Algebra (Default Framework) | Traditional Matrix Terminology | Category Theory Equivalent | Plain Description |
| :--- | :--- | :--- | :--- |
| **`Vexel` / `Box a`** | State Vector | Object (0-Cell) | Discrete multiset of basis keys $[(x, w)]$. |
| **`MaxelTransform a b`** | Matrix / Transition Table | 1-Cell ($T: a \to b$) | Multiset of pixel coordinate pairs $[((x, y), w)]$. |
| **`pushforward` ($f_*$) & `pullback` ($f^*$)** | Matrix-Vector Product | Galois Adjunction ($f_* \dashv f^*$) | Forward and transpose maxel-vexel operations. |
| **`composeMaxels` ($\circ$)** | Matrix Multiplication | 1-Cell Composition ($\mu$) | Pixel fusion composition $(T_1 \circ T_2)(x, z) = \sum_y T_1(x, y) \cdot T_2(y, z)$. |
| **`identityMaxel` ($I_a$)** | Identity Matrix | Adjunction Unit ($\eta$) | Diagonal pixel stream multiset $[((x, x), 1)]$. |
| **`maxelCommutator`** | Lie Bracket $[T_1, T_2]$ | Commutator 2-Cell | Net multiset difference $(T_1 \circ T_2) \ominus (T_2 \circ T_1)$. |
| **`UnixelFraction`** | Scalar Rational Number | Weight Coefficient | Exact rational observable $N / [D]$. |
| **`Boxel`** | 3D Volume Tensor | Higher Multicell | Multiset of 3D voxel coordinates $[(x, y, z), w]$. |

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`):

```bash
idris2 --build Idris2-Multiset-Transform.ipkg
idris2 --install Idris2-Multiset-Transform.ipkg
```

---

## 🔬 Language & Framework Integration

Written in **Idris 2** enforcing total constructivism (`%default total`).

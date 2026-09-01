# 🌀 Idris2-Multiset1

**Multiset Maxel Algebra, Pushforward/Pullback Operators & Discrete State Dynamics for Idris 2**

`Idris2-Multiset1` builds upon `Idris2-Multiset0` to implement discrete multiset **Maxel** algebra and linear state transformations. In accordance with Norman Wildberger's finitist physics, continuous/rigid matrices are replaced by **Maxels** (multisets of coordinate pixels) and **Vexels** (multisets of vector singletons):

- **Maxel Transforms (`MaxelTransform` / `TransformMultiset` / `Maxel`)**: Weighted multiset pixel tables $[((x, y), w)]$ mapping input Vexel densities to output Vexel densities across metric sectors.
- **Pushforward & Pullback Operators**:
  - **Pushforward (`pushforward` / `applyPushforwardContraction`)**: Forward maxel application multiplying input vexel counts by pixel weights: $(f_* M)(y) = \sum_x M(x) \cdot T(x, y)$.
  - **Pullback (`pullback` / `applyPullbackExpansion`)**: Transpose maxel application pulling target counts back to source keys: $(f^* N)(x) = \sum_y N(y) \cdot T(x, y)$.
- **Maxel Commutators (`maxelCommutator` / `commutatorTransforms`)**: $[T_1, T_2] = (T_1 \circ T_2) \ominus (T_2 \circ T_1)$ measuring directional maxel application order differences via exact multiset difference `subBox`.
- **Maxel Density Tables**: Symmetric state-pair maxels $\rho$ with exact diagonal trace normalization ($\text{Tr}(\rho) = \sum_x \rho(x, x)$) and partial trace extraction.
- **Boxel Contraction Networks**: Multi-dimensional boxel/voxel multiset contraction across matching pixel indices.

---

## 🔀 Maxel Algebra $\longleftrightarrow$ Matrix Terminology $\longleftrightarrow$ Category Theory

| Maxel Algebra (Default Framework) | Traditional Matrix Terminology | Category Theory Equivalent | Plain Description |
| :--- | :--- | :--- | :--- |
| **`Vexel` / `Box a`** | State Vector | Object (0-Cell) | Discrete multiset of basis keys $[(x, w)]$. |
| **`MaxelTransform a b`** | Matrix / Transition Table | 1-Cell ($T: a \to b$) | Multiset of pixel coordinate pairs $[((x, y), w)]$. |
| **`pushforward` ($f_*$) & `pullback` ($f^*$)** | Matrix-Vector Product | Galois Adjunction ($f_* \dashv f^*$) | Forward and transpose maxel-vexel operations. |
| **`multiplyMaxels` ($\circ$)** | Matrix Multiplication | 1-Cell Composition ($\mu$) | Pixel fusion composition $(T_1 \circ T_2)(x, z) = \sum_y T_1(x, y) \cdot T_2(y, z)$. |
| **`identityMaxel` ($I_a$)** | Identity Matrix | Adjunction Unit ($\eta$) | Diagonal pixel stream multiset $[((x, x), 1)]$. |
| **`maxelCommutator`** | Lie Bracket $[T_1, T_2]$ | Commutator 2-Cell | Net multiset difference $(T_1 \circ T_2) \ominus (T_2 \circ T_1)$. |
| **`Boxel`** | 3D Volume Tensor | Higher Multicell | Multiset of 3D voxel coordinates $[(x, y, z), w]$. |

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

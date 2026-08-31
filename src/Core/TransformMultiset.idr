module Core.TransformMultiset

import Core.BoxInt
import Core.Multiset
import Core.UnixelFraction
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. THE 4 METRIC GEOMETRY ENUMERATION FOR TRANSFORM MULTISETS
------------------------------------------------------------------------

||| The 4 canonical metric geometries governing spatial & gauge transformations.
public export
data MetricSector = EllipticSector | HyperbolicSector | ParabolicSector | SubstrateSector

public export
Eq MetricSector where
  EllipticSector == EllipticSector = True
  HyperbolicSector == HyperbolicSector = True
  ParabolicSector == ParabolicSector = True
  SubstrateSector == SubstrateSector = True
  _ == _ = False

------------------------------------------------------------------------
-- 2. UNIVERSAL TRANSFORM MULTISET FACTORIZATION RECORD (G ⊗ Z ⊗ J)
------------------------------------------------------------------------

||| A Universal Transform Multiset T_Law = G_{det g} ⊗ Z_{210} ⊗ Box (a, b)
||| unifying geometric signature, Primorial budget weighting, and data incidence multiset.
public export
record TransformMultiset (a : Type) (b : Type) where
  constructor MkTransformMultiset
  sector     : MetricSector     -- G_{det g}: Metric canvas signature
  fraction   : UnixelFraction   -- Z_{210}: Primorial rational budget weight
  matrixBox  : Box (a, b)       -- Pure Data Incidence Multiset: ((a, b), w)

------------------------------------------------------------------------
-- 3. HELPER CONSTRUCTORS & CONVERTERS
------------------------------------------------------------------------

||| Constructs a TransformMultiset from a list of incidence pairs ((a, b), w).
public export
mkTransformBox : MetricSector -> UnixelFraction -> List ((a, b), BoxInt) -> TransformMultiset a b
mkTransformBox sec frac pairs = MkTransformMultiset sec frac (MkBox pairs)

||| Transposes a TransformMultiset by swapping element coordinates (a, b) -> (b, a).
public export
transposeTransformBox : TransformMultiset a b -> TransformMultiset b a
transposeTransformBox (MkTransformMultiset sec frac (MkBox pairs)) =
  MkTransformMultiset sec frac (MkBox (map (\((a, b), w) => ((b, a), w)) pairs))

------------------------------------------------------------------------
-- 4. ALGEBRAIC TRANSFORM APPLICATION OPERATORS
------------------------------------------------------------------------

||| Evaluates multiset pushforward contraction (f_* M)(y) = ∑_{x} M(x) * T(x, y).
public export
applyPushforwardContraction : Eq a => Eq b => TransformMultiset a b -> Box a -> Box b
applyPushforwardContraction (MkTransformMultiset _ _ (MkBox tPairs)) state =
  foldl (\acc, ((a, b), wT) =>
           let wM = lookupBox a state
           in insertBox b (wM * wT) acc) emptyBox tPairs

||| Evaluates multiset pullback expansion (f^* N)(x) = ∑_{y} N(y) * T(x, y).
||| REQUIRES NO MANUAL DOMAIN LIST PARAMETER!
public export
applyPullbackExpansion : Eq a => Eq b => TransformMultiset a b -> Box b -> Box a
applyPullbackExpansion (MkTransformMultiset _ _ (MkBox tPairs)) macroState =
  foldl (\acc, ((a, b), wT) =>
           let wN = lookupBox b macroState
           in insertBox a (wN * wT) acc) emptyBox tPairs

------------------------------------------------------------------------
-- 5. MORPHISM OPERATORS FOR TENSOR COMPOSITION
------------------------------------------------------------------------

||| A Morphism Operator Multiset defining tensor composition rules.
public export
MorphismOperator : Type -> Type -> Type -> Type
MorphismOperator a b c = Box ((a, b), (b, c), (a, c))

||| Composes two TransformMultisets T1 and T2 using pure multiset matrix multiplication.
public export
composeTransforms : Eq a => Eq b => Eq c =>
                  TransformMultiset a b ->
                  TransformMultiset b c ->
                  TransformMultiset a c
composeTransforms (MkTransformMultiset s1 f1 (MkBox pairs1))
                  (MkTransformMultiset s2 f2 (MkBox pairs2)) =
  let composedPairs =
        foldl (\acc1, ((a, b1), w1) =>
                 foldl (\acc2, ((b2, c), w2) =>
                          if b1 == b2 then
                            insertBox (a, c) (w1 * w2) acc2
                          else acc2) acc1 pairs2) emptyBox pairs1
  in MkTransformMultiset s1 (mulUnixelFraction f1 f2) composedPairs

||| Evaluates higher-order 2-morphism operator contraction over two transform multisets:
||| α(T1, T2) => T3.
public export
applyMorphismOperator : Eq a => Eq b => Eq c =>
                        MorphismOperator a b c ->
                        TransformMultiset a b ->
                        TransformMultiset b c ->
                        TransformMultiset a c
applyMorphismOperator (MkBox opPairs) (MkTransformMultiset s1 f1 (MkBox t1Pairs)) (MkTransformMultiset s2 f2 (MkBox t2Pairs)) =
  let resPairs =
        foldl (\acc, (((a, b), (b2, c), (a2, c2)), wOp) =>
                 let w1 = lookupBox (a, b) (MkBox t1Pairs)
                     w2 = lookupBox (b2, c) (MkBox t2Pairs)
                     wProd = wOp * w1 * w2
                 in if (b == b2) && (a == a2) && (c == c2) && (unwrapBox wProd > 0)
                      then insertBox (a, c) wProd acc
                      else acc) emptyBox opPairs
  in MkTransformMultiset s1 (mulUnixelFraction f1 f2) resPairs

------------------------------------------------------------------------
-- 6. BRA-KET MULTISET INNER PRODUCT & DUALITY OPERATORS
------------------------------------------------------------------------

||| Computes the Bra-Ket multiset inner product <M1 | M2> = ∑_{x} M1(x) * M2(x).
public export
innerProductBox : Eq a => Box a -> Box a -> BoxInt
innerProductBox (MkBox items1) m2 =
  foldl (\acc, (x, w1) =>
           let w2 = lookupBox x m2
           in acc + (w1 * w2)) (intToBoxInt 0) items1

||| Computes the trace of an endomorphism transform multiset: Tr(T) = ∑_{x} T(x, x).
public export
traceTransform : Eq a => TransformMultiset a a -> BoxInt
traceTransform (MkTransformMultiset _ _ (MkBox tPairs)) =
  foldl (\acc, ((a, b), w) =>
           if a == b then acc + w else acc) (intToBoxInt 0) tPairs

------------------------------------------------------------------------
-- 7. CLOSED-FORM GALOIS ADJUNCTION KERNELS (η = T^T ∘ T, ε = T ∘ T^T)
------------------------------------------------------------------------

||| Computes the closed-form Galois Adjunction Unit Kernel Matrix η = T^T ∘ T ∈ Box (a, a).
public export
adjunctionUnitKernel : Eq a => Eq b => TransformMultiset a b -> TransformMultiset a a
adjunctionUnitKernel t = composeTransforms t (transposeTransformBox t)

||| Computes the closed-form Galois Adjunction Counit Kernel Matrix ε = T ∘ T^T ∈ Box (b, b).
public export
adjunctionCounitKernel : Eq a => Eq b => TransformMultiset a b -> TransformMultiset b b
adjunctionCounitKernel t = composeTransforms (transposeTransformBox t) t

------------------------------------------------------------------------
-- 8. SPECTRAL MULTISET POWER ITERATION SOLVER
------------------------------------------------------------------------

||| Computes the Perron-Frobenius stationary ground state distribution of an endomorphism
||| transform multiset via power iteration under structural fuel bounds.
public export
computeStationaryDistribution : Eq a => TransformMultiset a a -> Nat -> Box a -> Box a
computeStationaryDistribution transform 0 initial = initial
computeStationaryDistribution transform (S fuel) initial =
  let nextState = applyPushforwardContraction transform initial
  in computeStationaryDistribution transform fuel nextState

------------------------------------------------------------------------
-- 9. UNITARY CLASS & LIE COMMUTATOR TENSOR DERIVATIONS
------------------------------------------------------------------------

||| Constructs an Identity Transform Multiset I_a over a given domain list.
public export
identityTransform : Eq a => List a -> TransformMultiset a a
identityTransform domain =
  mkTransformBox EllipticSector unitUnixelFraction (map (\x => ((x, x), intToBoxInt 1)) domain)

||| Classifies whether a transform T: a -> b is a Unitary Isomorphism (η = I_a and ε = I_b).
public export
isUnitaryTransform : Eq a => Eq b => List a -> List b -> TransformMultiset a b -> Bool
isUnitaryTransform domainA domainB t =
  let eta = adjunctionUnitKernel t
      eps = adjunctionCounitKernel t
      idA = identityTransform domainA
      idB = identityTransform domainB
  in (eta.matrixBox == idA.matrixBox) && (eps.matrixBox == idB.matrixBox)

||| Computes the Lie Bracket Commutator Matrix [T1, T2] = (T1 ∘ T2) ⊖ (T2 ∘ T1).
public export
commutatorTransforms : Eq a => TransformMultiset a a -> TransformMultiset a a -> TransformMultiset a a
commutatorTransforms t1 t2 =
  let t12 = composeTransforms t1 t2
      t21 = composeTransforms t2 t1
  in MkTransformMultiset t1.sector t1.fraction (subBox t12.matrixBox t21.matrixBox)

------------------------------------------------------------------------
-- 10. QUANTUM DENSITY MATRIX PARTIAL TRACE & HYPER-TENSORS (MPS/PEPS)
------------------------------------------------------------------------

||| Evaluates the Partial Trace ρ_A = Tr_B(ρ_AB) over composite multiset pairs.
public export
partialTraceBox : Eq a => Eq b => Box (a, b) -> Box a
partialTraceBox (MkBox items) =
  foldl (\acc, ((a, b), w) => insertBox a w acc) emptyBox items

||| A Multiset Hyper-Tensor of rank k over carrier type a.
public export
HyperTensor : Nat -> Type -> Type
HyperTensor k a = Box (Vect k a)

||| Contracts two 2D Multiset Hyper-Tensors into a 2D composite multiset.
public export
contractHyperTensor : Eq a => HyperTensor 2 a -> HyperTensor 2 a -> Box (a, a)
contractHyperTensor (MkBox items1) (MkBox items2) =
  foldl (\acc1, ([a, b1], w1) =>
           foldl (\acc2, ([b2, c], w2) =>
                    if b1 == b2 then insertBox (a, c) (w1 * w2) acc2 else acc2) acc1 items2) emptyBox items1

------------------------------------------------------------------------
-- 6. INVARIANT AUDIT WITNESSES
------------------------------------------------------------------------

||| Audits that TransformMultiset identity application preserves multiset token counts.
public export
auditTransformMultisetIdentityProof : Bool
auditTransformMultisetIdentityProof =
  let tId : TransformMultiset Nat Nat = mkTransformBox EllipticSector unitUnixelFraction [((1, 1), intToBoxInt 1)]
      m : Box Nat = insertBox 1 (intToBoxInt 3) emptyBox
      pushed = applyPushforwardContraction tId m
  in lookupBox 1 pushed == intToBoxInt 3

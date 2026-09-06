module Core.TransformMultiset

import public Core.BoxInt
import public Core.Multiset
import public Core.UnixelFraction
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. THE 4 METRIC GEOMETRY ENUMERATION FOR MAXEL TRANSFORMS
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
-- 2. UNIVERSAL MAXEL TRANSFORM RECORD (G_{det g} ⊗ Z_{210} ⊗ Box (a, b))
------------------------------------------------------------------------

||| A Universal Maxel Transform T_Law = G_{det g} ⊗ Z_{210} ⊗ Box (a, b)
||| unifying geometric signature, Primorial budget weighting, and pixel incidence multiset.
public export
record MaxelTransform (a : Type) (b : Type) where
  constructor MkMaxelTransform
  sector   : MetricSector     -- G_{det g}: Metric canvas signature
  fraction : UnixelFraction   -- Z_{210}: Primorial rational budget weight
  pixelBox : Box (a, b)       -- Pure Pixel Incidence Multiset: ((a, b), w)

-- Backwards Compatibility Aliases
public export
TransformMultiset : Type -> Type -> Type
TransformMultiset = MaxelTransform

public export
MkTransformMultiset : MetricSector -> UnixelFraction -> Box (a, b) -> MaxelTransform a b
MkTransformMultiset = MkMaxelTransform

------------------------------------------------------------------------
-- 3. HELPER CONSTRUCTORS & CONVERTERS
------------------------------------------------------------------------

||| Constructs a MaxelTransform from a list of pixel incidence pairs ((a, b), w).
public export
mkMaxelTransform : MetricSector -> UnixelFraction -> List ((a, b), BoxInt) -> MaxelTransform a b
mkMaxelTransform sec frac pairs = MkMaxelTransform sec frac (MkBox pairs)

public export
mkTransformBox : MetricSector -> UnixelFraction -> List ((a, b), BoxInt) -> MaxelTransform a b
mkTransformBox = mkMaxelTransform

||| Transposes a MaxelTransform by swapping pixel coordinates (a, b) -> (b, a).
public export
transposeMaxel : MaxelTransform a b -> MaxelTransform b a
transposeMaxel (MkMaxelTransform sec frac (MkBox pairs)) =
  MkMaxelTransform sec frac (MkBox (map (\((a, b), w) => ((b, a), w)) pairs))

public export
transposeTransformBox : MaxelTransform a b -> MaxelTransform b a
transposeTransformBox = transposeMaxel

------------------------------------------------------------------------
-- 4. ALGEBRAIC MAXEL PUSHFORWARD & PULLBACK OPERATORS
------------------------------------------------------------------------

||| Evaluates multiset pushforward contraction (f_* M)(y) = ∑_{x} M(x) * T(x, y).
public export
applyPushforward : Eq a => Eq b => MaxelTransform a b -> Box a -> Box b
applyPushforward (MkMaxelTransform _ _ (MkBox tPairs)) state =
  foldl (\acc, ((a, b), wT) =>
           let wM = lookupBox a state
           in insertBox b (wM * wT) acc) emptyBox tPairs

public export
applyPushforwardContraction : Eq a => Eq b => MaxelTransform a b -> Box a -> Box b
applyPushforwardContraction = applyPushforward

public export
pushforward : Eq a => Eq b => MaxelTransform a b -> Box a -> Box b
pushforward = applyPushforward

||| Evaluates multiset pullback expansion (f^* N)(x) = ∑_{y} N(y) * T(x, y).
public export
applyPullback : Eq a => Eq b => MaxelTransform a b -> Box b -> Box a
applyPullback (MkMaxelTransform _ _ (MkBox tPairs)) macroState =
  foldl (\acc, ((a, b), wT) =>
           let wN = lookupBox b macroState
           in insertBox a (wN * wT) acc) emptyBox tPairs

public export
applyPullbackExpansion : Eq a => Eq b => MaxelTransform a b -> Box b -> Box a
applyPullbackExpansion = applyPullback

public export
pullback : Eq a => Eq b => MaxelTransform a b -> Box b -> Box a
pullback = applyPullback

------------------------------------------------------------------------
-- 5. MAXEL PIXEL FUSION COMPOSITION
------------------------------------------------------------------------

||| A Morphism Operator Multiset defining tensor composition rules.
public export
MorphismOperator : Type -> Type -> Type -> Type
MorphismOperator a b c = Box ((a, b), (b, c), (a, c))

||| Composes two MaxelTransforms T1 and T2 using pixel fusion multiplication.
public export
composeMaxels : Eq a => Eq b => Eq c =>
                MaxelTransform a b ->
                MaxelTransform b c ->
                MaxelTransform a c
composeMaxels (MkMaxelTransform s1 f1 (MkBox pairs1))
              (MkMaxelTransform s2 f2 (MkBox pairs2)) =
  let composedPairs =
        foldl (\acc1, ((a, b1), w1) =>
                 foldl (\acc2, ((b2, c), w2) =>
                          if b1 == b2 then
                            insertBox (a, c) (w1 * w2) acc2
                          else acc2) acc1 pairs2) emptyBox pairs1
  in MkMaxelTransform s1 (mulUnixelFraction f1 f2) composedPairs

public export
composeTransforms : Eq a => Eq b => Eq c =>
                  MaxelTransform a b ->
                  MaxelTransform b c ->
                  MaxelTransform a c
composeTransforms = composeMaxels

public export
multiplyMaxels : Eq a => Eq b => Eq c => MaxelTransform a b -> MaxelTransform b c -> MaxelTransform a c
multiplyMaxels = composeMaxels

||| Evaluates higher-order operator contraction over two maxel transforms.
public export
applyMorphismOperator : Eq a => Eq b => Eq c =>
                        MorphismOperator a b c ->
                        MaxelTransform a b ->
                        MaxelTransform b c ->
                        MaxelTransform a c
applyMorphismOperator (MkBox opPairs) (MkMaxelTransform s1 f1 (MkBox t1Pairs)) (MkMaxelTransform s2 f2 (MkBox t2Pairs)) =
  let resPairs =
        foldl (\acc, (((a, b), (b2, c), (a2, c2)), wOp) =>
                 let w1 = lookupBox (a, b) (MkBox t1Pairs)
                     w2 = lookupBox (b2, c) (MkBox t2Pairs)
                     wProd = wOp * w1 * w2
                 in if (b == b2) && (a == a2) && (c == c2) && (unwrapBox wProd > 0)
                      then insertBox (a, c) wProd acc
                      else acc) emptyBox opPairs
  in MkMaxelTransform s1 (mulUnixelFraction f1 f2) resPairs

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

||| Computes the trace of an endomorphism maxel transform: Tr(T) = ∑_{x} T(x, x).
public export
traceMaxel : Eq a => MaxelTransform a a -> BoxInt
traceMaxel (MkMaxelTransform _ _ (MkBox tPairs)) =
  foldl (\acc, ((a, b), w) =>
           if a == b then acc + w else acc) (intToBoxInt 0) tPairs

public export
traceTransform : Eq a => MaxelTransform a a -> BoxInt
traceTransform = traceMaxel

------------------------------------------------------------------------
-- 7. GALOIS ADJUNCTION KERNELS (η = T^T ∘ T, ε = T ∘ T^T)
------------------------------------------------------------------------

||| Computes the closed-form Galois Adjunction Unit Kernel Matrix η = T^T ∘ T ∈ Box (a, a).
public export
adjunctionUnitKernel : Eq a => Eq b => MaxelTransform a b -> MaxelTransform a a
adjunctionUnitKernel t = composeMaxels t (transposeMaxel t)

||| Computes the closed-form Galois Adjunction Counit Kernel Matrix ε = T ∘ T^T ∈ Box (b, b).
public export
adjunctionCounitKernel : Eq a => Eq b => MaxelTransform a b -> MaxelTransform b b
adjunctionCounitKernel t = composeMaxels (transposeMaxel t) t

------------------------------------------------------------------------
------------------------------------------------------------------------
-- 8. UNITARY CLASS & COMMUTATOR DERIVATIONS
------------------------------------------------------------------------

||| Constructs an Identity MaxelTransform I_a over a given domain list.
public export
identityMaxel : Eq a => List a -> MaxelTransform a a
identityMaxel domain =
  mkMaxelTransform EllipticSector unitUnixelFraction (map (\x => ((x, x), intToBoxInt 1)) domain)

public export
identityTransform : Eq a => List a -> MaxelTransform a a
identityTransform = identityMaxel

------------------------------------------------------------------------
-- 9. SPECTRAL MULTISET POWER ITERATION SOLVER
------------------------------------------------------------------------

||| Computes the Perron-Frobenius stationary ground state distribution of an endomorphism
||| maxel transform via power iteration under structural fuel bounds.
public export
computeStationaryDistribution : Eq a => MaxelTransform a a -> Nat -> Box a -> Box a
computeStationaryDistribution transform 0 initial = initial
computeStationaryDistribution transform (S fuel) initial =
  let nextState = applyPushforward transform initial
  in computeStationaryDistribution transform fuel nextState

||| Classifies whether a transform T: a -> b is a Unitary Isomorphism (η = I_a and ε = I_b).
public export
isUnitaryMaxel : Eq a => Eq b => List a -> List b -> MaxelTransform a b -> Bool
isUnitaryMaxel domainA domainB t =
  let eta = adjunctionUnitKernel t
      eps = adjunctionCounitKernel t
      idA = identityMaxel domainA
      idB = identityMaxel domainB
  in (eta.pixelBox == idA.pixelBox) && (eps.pixelBox == idB.pixelBox)

public export
isUnitaryTransform : Eq a => Eq b => List a -> List b -> MaxelTransform a b -> Bool
isUnitaryTransform = isUnitaryMaxel

||| Computes the Commutator Maxel Difference [T1, T2] = (T1 ∘ T2) ⊖ (T2 ∘ T1).
public export
commutatorMaxels : Eq a => MaxelTransform a a -> MaxelTransform a a -> MaxelTransform a a
commutatorMaxels t1 t2 =
  let t12 = composeMaxels t1 t2
      t21 = composeMaxels t2 t1
  in MkMaxelTransform t1.sector t1.fraction (subBox t12.pixelBox t21.pixelBox)

public export
commutatorTransforms : Eq a => MaxelTransform a a -> MaxelTransform a a -> MaxelTransform a a
commutatorTransforms = commutatorMaxels

public export
maxelCommutator : Eq a => MaxelTransform a a -> MaxelTransform a a -> MaxelTransform a a
maxelCommutator = commutatorMaxels

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
-- 11. INVARIANT AUDIT WITNESSES
------------------------------------------------------------------------

||| Audits that MaxelTransform identity application preserves multiset token counts.
public export
auditTransformMultisetIdentityProof : Bool
auditTransformMultisetIdentityProof =
  let tId : MaxelTransform Nat Nat = mkMaxelTransform EllipticSector unitUnixelFraction [((1, 1), intToBoxInt 1)]
      m : Box Nat = insertBox 1 (intToBoxInt 3) emptyBox
      pushed = applyPushforward tId m
  in lookupBox 1 pushed == intToBoxInt 3

||| Structurally total split function dividing a list into two smaller halves.
public export
splitHalf : List a -> (List a, List a)
splitHalf [] = ([], [])
splitHalf [x] = ([x], [])
splitHalf (x :: y :: rest) =
  let (xs, ys) = splitHalf rest
  in (x :: xs, y :: ys)

||| Top-level structurally total branch evaluator for parallel pushforward tree reduction.
public export
evalTransformBranch : Eq a => Eq b => (fuel : Nat) -> List ((a, b), BoxInt) -> Box a -> Box b
evalTransformBranch Z _ _ = emptyBox
evalTransformBranch (S _) [] _ = emptyBox
evalTransformBranch (S _) [((a, b), wT)] state =
  let wM = lookupBox a state
  in insertBox b (wM * wT) emptyBox
evalTransformBranch (S k) (p1 :: p2 :: rest) state =
  let (leftBranch, rightBranch) = splitHalf (p1 :: p2 :: rest)
  in unionBox (evalTransformBranch k leftBranch state) (evalTransformBranch k rightBranch state)

||| Evaluates multiset pushforward contraction using divide-and-conquer parallel tree reduction.
public export
applyPushforwardParallel : Eq a => Eq b => MaxelTransform a b -> Box a -> Box b
applyPushforwardParallel (MkMaxelTransform _ _ (MkBox tPairs)) state =
  evalTransformBranch (length tPairs + 10) tPairs state

||| Audits the equality between parallel tree reduction and sequential pushforward contraction.
public export
auditParallelPushforwardProof : Bool
auditParallelPushforwardProof =
  let t : MaxelTransform Nat Nat = mkMaxelTransform EllipticSector unitUnixelFraction [((1, 1), intToBoxInt 2), ((2, 2), intToBoxInt 3)]
      m : Box Nat = insertBox 1 (intToBoxInt 5) (insertBox 2 (intToBoxInt 7) emptyBox)
      seqOut = applyPushforward t m
      parOut = applyPushforwardParallel t m
  in (lookupBox 1 seqOut == lookupBox 1 parOut) && (lookupBox 2 seqOut == lookupBox 2 parOut)

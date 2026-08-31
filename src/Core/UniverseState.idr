module Core.UniverseState

import Core.BoxInt
import Core.Multiset
import Core.VexelMaxel
import Data.Vect

%default total

||| The completely un-hardcoded cosmic partition state.
||| Dimensions are tracked relationally through dependent parameters.
||| All data slots store exact BoxInt discrete particle/quadrance tokens.
public export
record UniverseState (vmSize : Nat) (deSize : Nat) (dmSize : Nat) where
  constructor MkUniverseState
  visibleMatter : Vect vmSize BoxInt -- Active spatial field lattice
  darkEnergy    : Vect deSize BoxInt -- Background ROM capacity
  darkMatter    : Vect dmSize BoxInt -- Historical error/residue ledger

||| Extracts the Dark Matter log as a read-only reference.
public export
dmLog : UniverseState vm de dm -> Vect dm BoxInt
dmLog (MkUniverseState _ _ dmData) = dmData

||| Calculates total active state energy across all memory pools.
public export
totalStateCapacity : {vm, de, dm : Nat} -> UniverseState vm de dm -> Nat
totalStateCapacity {vm} {de} {dm} _ = vm + de + dm

||| Seed constructor for a vacuum state with 0 values across memory pools.
public export
seedCosmicVacuum : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> UniverseState vm de dm
seedCosmicVacuum vm de dm = MkUniverseState (replicate vm (intToBoxInt 0)) (replicate de (intToBoxInt 0)) (replicate dm (intToBoxInt 0))

||| Linear vector combination appending two Vect states.
public export
linearVectCombine : Vect n a -> Vect m a -> Vect (n + m) a
linearVectCombine [] r = r
linearVectCombine (x :: xs) r = x :: linearVectCombine xs r

------------------------------------------------------------------------
-- UNIFIED COSMIC DIRECT-SUM MULTISET
------------------------------------------------------------------------

||| The Unified Cosmic Multiset:
||| Encodes Visible Matter as a 3D Boxel (27 cells), Dark Energy as a 2D Maxel (128 cells),
||| and Dark Matter as an inductive 1D Vexel of historical singletons.
public export
record CosmicMultiset where
  constructor MkCosmicMultiset
  visible    : Boxel
  darkEnergy : Maxel
  darkMatter : Vexel

||| Calculates total active state energy across the cosmic multiset.
public export
totalCosmicMultisetBudget : CosmicMultiset -> Nat
totalCosmicMultisetBudget (MkCosmicMultiset (MkBoxel v) (MkMaxel de) (MkVexel dm)) =
  length v + length de + length dm

||| Embeds a dependent UniverseState into the Unified Cosmic Multiset.
public export
stateToCosmicMultiset : {vm, de, dm : Nat} -> UniverseState vm de dm -> CosmicMultiset
stateToCosmicMultiset (MkUniverseState vmVect deVect dmVect) =
  let vmTerms = toList (tabulate (\idx => (MkVoxel (finToNat idx + 1) 1 1, index idx vmVect)))
      deTerms = toList (tabulate (\idx => (MkPixel (finToNat idx + 1) 1, index idx deVect)))
      dmTerms = toList (tabulate (\idx => (MkUnixel (finToNat idx + 1), index idx dmVect)))
  in MkCosmicMultiset (canonicalizeBoxel (MkBoxel vmTerms)) (canonicalizeMaxel (MkMaxel deTerms)) (canonicalizeVexel (MkVexel dmTerms))

||| Audits that Epoch 37 CosmicMultiset has total budget 210 = 27 + 128 + 55.
public export
auditCosmicMultisetBudgetProof : Bool
auditCosmicMultisetBudgetProof =
  let mockState = MkUniverseState {vmSize=27} {deSize=128} {dmSize=55}
                    (replicate 27 (intToBoxInt 1))
                    (replicate 128 (intToBoxInt 1))
                    (replicate 55 (intToBoxInt 1))
      cMultiset = stateToCosmicMultiset mockState
  in totalCosmicMultisetBudget cMultiset == 210

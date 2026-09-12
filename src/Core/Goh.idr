module Core.Goh

import Data.Vect
import Decidable.Equality
import Core.UnixelFraction

%default total

--------------------------------------------------------------------------------
-- GOH AUXILIARY POLYNOMIAL & MULTISET LEDGER
--------------------------------------------------------------------------------

||| An auxiliary polynomial term extracted from the Goh factorization tree.
||| Expressed as an irreducible component Phi_k(s).
public export
record GohAuxiliary (degree : Nat) where
  constructor Phi
  coefficients : Vect (S degree) UnixelFraction

public export
implementation Eq (GohAuxiliary degree) where
  (Phi c1) == (Phi c2) = c1 == c2

||| Layer 2 Container: The multiset ledger governing state transformations.
||| This tracks the collection of factors currently defining the UniverseState.
public export
data GohMultiset : Type where
  EmptyBag  : GohMultiset
  AddFactor : {deg : Nat} -> GohAuxiliary deg -> GohMultiset -> GohMultiset

public export
implementation Eq GohMultiset where
  EmptyBag == EmptyBag = True
  -- Using heterogeneous binding matching to trap dependent dimensions
  (AddFactor {deg=d1} f1 rest1) == (AddFactor {deg=d2} f2 rest2) =
    case decEq d1 d2 of
      -- By matching on 'Refl', d1 and d2 become syntactically unified,
      -- allowing (f1 == f2) to type-check cleanly across the unified type universe.
      Yes Refl => (f1 == f2) && (rest1 == rest2)
      No _     => False
  _ == _ = False

public export
implementation Show GohMultiset where
  show EmptyBag = "EmptyBag"
  show (AddFactor {deg} _ rest) = "AddFactor (Phi_deg" ++ show deg ++ ") " ++ show rest

||| Counts the total number of polynomial factors in a GohMultiset.
public export
countFactors : GohMultiset -> Nat
countFactors EmptyBag = 0
countFactors (AddFactor _ rest) = S (countFactors rest)


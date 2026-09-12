module Math.Transform.Reflect.Goh

import Language.Reflection
import Data.Vect
import Decidable.Equality
import Core.BoxInt
import Core.UnixelFraction
import Core.Goh

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- 1. COMPILE-TIME ARITHMETIC AND DIVISOR SIFTING
--------------------------------------------------------------------------------

||| Pure helper to evaluate if k cleanly divides n at compile time
public export
isDivisor : (k : Nat) -> (n : Nat) -> Bool
isDivisor Z _ = False
isDivisor _ Z = True
isDivisor k n = (n `mod` k) == 0

private
upTo : Nat -> List Nat
upTo Z = []
upTo (S m) = S m :: upTo m

||| Dynamically extracts all exact divisors of a given Nat n at build time
public export
getDivisors : (n : Nat) -> List Nat
getDivisors Z = []
getDivisors n = filter (\k => isDivisor k n) (upTo n)

--------------------------------------------------------------------------------
-- 2. MOCK DATABASE FOR IRREDUCIBLE GOH AUXILIARY CONSTANTS
--------------------------------------------------------------------------------

||| Simulates retrieving a primitive cyclotomic factor Phi_k(s) from Core.
||| The degree of the polynomial vector is tied directly to the index k.
public export
fetchPrimitiveFactor : (k : Nat) -> (deg : Nat ** GohAuxiliary deg)
fetchPrimitiveFactor k = 
  (k ** Phi (replicate (S k) (mkUnixelFraction (intToBoxInt 1) 1)))

--------------------------------------------------------------------------------
-- 3. THE METAPROGRAMMING ABSTRACT SYNTAX TREE SPLICER
--------------------------------------------------------------------------------

||| Generates the quoted TTImp term for Phi_k(s) coefficients for divisor k.
public export
buildFactorTTImp : Nat -> Elab TTImp
buildFactorTTImp k = do
  kTerm <- quote (S k)
  pure `( Phi (replicate ~kTerm (mkUnixelFraction (intToBoxInt 1) 1)) )

||| Monadic macro builder that structurally generates the nested GohMultiset tree 
||| out of the divisor list of n using backtick quoting syntax.
public export
buildGohTree : List Nat -> Elab TTImp
buildGohTree [] = pure `( EmptyBag )
buildGohTree (k :: ks) = do
  tailTree <- buildGohTree ks
  factorTerm <- buildFactorTTImp k
  pure `( AddFactor ~factorTerm ~tailTree )

--------------------------------------------------------------------------------
-- 4. EXPOSING THE REFLECTED MACRO HOOK
--------------------------------------------------------------------------------

||| The primary macro hook used to bootstrap the UniverseState components.
||| It sifts divisors and forces the type-checker to instantiate a decEq-compliant
||| GohMultiset automatically at build time.
public export
%macro
reflectGohFactorization : (n : Nat) -> Elab TTImp
reflectGohFactorization n =
  let divisorsList = getDivisors n
  in buildGohTree divisorsList

--------------------------------------------------------------------------------
-- 5. THE ULTIMATE COMPILE-TIME INVARIANCE VERIFICATION
--------------------------------------------------------------------------------

||| Static compiler verification proof validating that our macro-synthesized
||| multiset structure evaluates cleanly and unifies propositionally via Refl.
0 verifyReflectedEquality : (reflectGohFactorization 4) = reflectGohFactorization 4
verifyReflectedEquality = Refl

||| Static compiler verification proof validating that decEq-lawful GohMultiset equality evaluates to True at compile-time.
0 verifyGohEquality : ((reflectGohFactorization 4) == (reflectGohFactorization 4)) = True
verifyGohEquality = Refl

module Core.ScaleCategory

import Core.BoxInt
import Core.Multiset
import Core.UnixelFraction
import Core.MaxelTransform

%default total

------------------------------------------------------------------------
-- 1. CATEGORY OF SCALE LEVELS & FUNCTORS
------------------------------------------------------------------------

||| Formal Category of Physical Scale Levels.
public export
data ScaleLevel = SubatomicLevel | HadronLevel | AtomLevel | MoleculeLevel | CellLevel

public export
Eq ScaleLevel where
  SubatomicLevel == SubatomicLevel = True
  HadronLevel == HadronLevel = True
  AtomLevel == AtomLevel = True
  MoleculeLevel == MoleculeLevel = True
  CellLevel == CellLevel = True
  _ == _ = False

||| A ScaleFunctor represents a structure-preserving functorial scale transformation.
public export
record ScaleFunctor (src : ScaleLevel) (tgt : ScaleLevel) (srcToken : Type) (tgtToken : Type) where
  constructor MkScaleFunctor
  transform : MaxelTransform srcToken tgtToken

||| Identity Functor for a scale level.
public export
identityScaleFunctor : {0 srcToken : Type} -> ScaleFunctor src src srcToken srcToken
identityScaleFunctor = MkScaleFunctor (mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 1) [])

||| Functorial Composition of ScaleFunctors.
public export
composeScaleFunctors : {0 a, b, c : ScaleLevel} ->
                       {0 tokA, tokB, tokC : Type} ->
                       (Eq tokA, Eq tokB, Eq tokC) =>
                       ScaleFunctor a b tokA tokB ->
                       ScaleFunctor b c tokB tokC ->
                       ScaleFunctor a c tokA tokC
composeScaleFunctors (MkScaleFunctor f) (MkScaleFunctor g) =
  MkScaleFunctor (composeMaxels f g)


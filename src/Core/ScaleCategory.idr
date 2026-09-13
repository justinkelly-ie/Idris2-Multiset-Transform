module Core.ScaleCategory

import Core.BoxInt
import Core.Multiset
import Core.UnixelFraction
import Core.TransformMultiset
import Core.ScalePipeline

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

------------------------------------------------------------------------
-- 2. LAYER 1 CANONICAL SCALE FUNCTORS
------------------------------------------------------------------------

public export
sf1_QuarkToHadron : ScaleFunctor SubatomicLevel HadronLevel ColorCharge HadronToken
sf1_QuarkToHadron = MkScaleFunctor t1_QuarkToHadron

public export
sf2_HadronToAtom : ScaleFunctor HadronLevel AtomLevel HadronToken AtomToken
sf2_HadronToAtom = MkScaleFunctor t2_HadronToAtom

public export
sf3_AtomToMolecule : ScaleFunctor AtomLevel MoleculeLevel AtomToken MoleculeToken
sf3_AtomToMolecule = MkScaleFunctor t3_AtomToMolecule

public export
sf4_MoleculeToBiomodule : ScaleFunctor MoleculeLevel CellLevel MoleculeToken BiomoduleToken
sf4_MoleculeToBiomodule = MkScaleFunctor t4_MoleculeToBiomodule

public export
sfTotalFunctorialPipeline : ScaleFunctor SubatomicLevel CellLevel ColorCharge BiomoduleToken
sfTotalFunctorialPipeline = composeScaleFunctors (composeScaleFunctors (composeScaleFunctors sf1_QuarkToHadron sf2_HadronToAtom) sf3_AtomToMolecule) sf4_MoleculeToBiomodule

module Core.ScalePipeline

import Core.BoxInt
import Core.Multiset
import Core.UnixelFraction
import Core.TransformMultiset
import Core.ScaleCategory
import Data.List

%default total

------------------------------------------------------------------------
-- 1. FULL STANDARD MODEL SUBATOMIC CARRIER TOKENS (SCALE LEVEL 1)
------------------------------------------------------------------------

||| Standard Model Quark Flavors
public export
data QuarkFlavor = UpQuark | DownQuark | StrangeQuark | CharmQuark | BottomQuark | TopQuark

public export
Eq QuarkFlavor where
  UpQuark == UpQuark = True
  DownQuark == DownQuark = True
  StrangeQuark == StrangeQuark = True
  CharmQuark == CharmQuark = True
  BottomQuark == BottomQuark = True
  TopQuark == TopQuark = True
  _ == _ = False

||| Standard Model Lepton Flavors
public export
data LeptonFlavor = ElectronToken | MuonToken | TauToken | ElectronNeutrinoToken | MuonNeutrinoToken | TauNeutrinoToken

public export
Eq LeptonFlavor where
  ElectronToken == ElectronToken = True
  MuonToken == MuonToken = True
  TauToken == TauToken = True
  ElectronNeutrinoToken == ElectronNeutrinoToken = True
  MuonNeutrinoToken == MuonNeutrinoToken = True
  TauNeutrinoToken == TauNeutrinoToken = True
  _ == _ = False

||| Standard Model Gauge & Scalar Bosons including 8 SU(3) Gell-Mann Gluon Octet States
public export
data GaugeBoson = PhotonToken 
                | GluonToken 
                | GluonOctet1 | GluonOctet2 | GluonOctet3 | GluonOctet4 
                | GluonOctet5 | GluonOctet6 | GluonOctet7 | GluonOctet8
                | WBosonPlusToken | WBosonMinusToken | ZBosonToken | HiggsBosonToken

public export
Eq GaugeBoson where
  PhotonToken == PhotonToken = True
  GluonToken == GluonToken = True
  GluonOctet1 == GluonOctet1 = True
  GluonOctet2 == GluonOctet2 = True
  GluonOctet3 == GluonOctet3 = True
  GluonOctet4 == GluonOctet4 = True
  GluonOctet5 == GluonOctet5 = True
  GluonOctet6 == GluonOctet6 = True
  GluonOctet7 == GluonOctet7 = True
  GluonOctet8 == GluonOctet8 = True
  WBosonPlusToken == WBosonPlusToken = True
  WBosonMinusToken == WBosonMinusToken = True
  ZBosonToken == ZBosonToken = True
  HiggsBosonToken == HiggsBosonToken = True
  _ == _ = False

||| Scale Level 1 Subatomic Particles (Quarks, Leptons, Bosons & Color Charges)
public export
data SubatomicParticle = QuarkToken QuarkFlavor | LeptonToken LeptonFlavor | BosonToken GaugeBoson

public export
Eq SubatomicParticle where
  (QuarkToken q1) == (QuarkToken q2) = q1 == q2
  (LeptonToken l1) == (LeptonToken l2) = l1 == l2
  (BosonToken b1) == (BosonToken b2) = b1 == b2
  _ == _ = False

||| Legacy Subatomic Color Charge Tokens
public export
data ColorCharge = RedColor | GreenColor | BlueColor

public export
Eq ColorCharge where
  RedColor == RedColor = True
  GreenColor == GreenColor = True
  BlueColor == BlueColor = True
  _ == _ = False

------------------------------------------------------------------------
-- 2. HADRONIC NUCLEON & MESON TOKENS (SCALE LEVEL 2)
------------------------------------------------------------------------

||| Scale Level 2: Hadronic Nucleons, Hyperons, Mesons & Vector Resonances
public export
data HadronToken = ProtonToken 
                 | NeutronToken 
                 | LambdaBaryonToken 
                 | SigmaBaryonToken 
                 | XiBaryonToken 
                 | OmegaBaryonToken
                 | PionPlusToken 
                 | PionMinusToken 
                 | NeutralPionToken
                 | KaonPlusToken
                 | KaonMinusToken
                 | NeutralKaonToken
                 | RhoMesonToken
                 | JPsiMesonToken
                 | UpsilonMesonToken

public export
Eq HadronToken where
  ProtonToken == ProtonToken = True
  NeutronToken == NeutronToken = True
  LambdaBaryonToken == LambdaBaryonToken = True
  SigmaBaryonToken == SigmaBaryonToken = True
  XiBaryonToken == XiBaryonToken = True
  OmegaBaryonToken == OmegaBaryonToken = True
  PionPlusToken == PionPlusToken = True
  PionMinusToken == PionMinusToken = True
  NeutralPionToken == NeutralPionToken = True
  KaonPlusToken == KaonPlusToken = True
  KaonMinusToken == KaonMinusToken = True
  NeutralKaonToken == NeutralKaonToken = True
  RhoMesonToken == RhoMesonToken = True
  JPsiMesonToken == JPsiMesonToken = True
  UpsilonMesonToken == UpsilonMesonToken = True
  _ == _ = False

------------------------------------------------------------------------
-- 3. ATOMIC ELEMENT TOKENS (SCALE LEVEL 3)
------------------------------------------------------------------------

||| Scale Level 3: Atomic Elements
public export
data AtomToken = HydrogenToken | HeliumToken | CarbonToken | NitrogenToken | OxygenToken | PhosphorusToken | SulfurToken | IronToken

public export
Eq AtomToken where
  HydrogenToken == HydrogenToken = True
  HeliumToken == HeliumToken = True
  CarbonToken == CarbonToken = True
  NitrogenToken == NitrogenToken = True
  OxygenToken == OxygenToken = True
  PhosphorusToken == PhosphorusToken = True
  SulfurToken == SulfurToken = True
  IronToken == IronToken = True
  _ == _ = False

------------------------------------------------------------------------
-- 4. MOLECULAR SPECIES TOKENS (SCALE LEVEL 4)
------------------------------------------------------------------------

||| Scale Level 4: Molecular Species & Bioenergetic Compounds
public export
data MoleculeToken = WaterMoleculeToken | CarbonDioxideToken | MethaneToken | AmmoniaToken | ATPBioToken

public export
Eq MoleculeToken where
  WaterMoleculeToken == WaterMoleculeToken = True
  CarbonDioxideToken == CarbonDioxideToken = True
  MethaneToken == MethaneToken = True
  AmmoniaToken == AmmoniaToken = True
  ATPBioToken == ATPBioToken = True
  _ == _ = False

------------------------------------------------------------------------
-- 5. CELLULAR BIOMODULE TOKENS (SCALE LEVEL 5)
------------------------------------------------------------------------

||| Scale Level 5: Macromolecular Nucleotides & Cellular Biomodules
public export
data BiomoduleToken = AdenineToken | ThymineToken | GuanineToken | CytosineToken | HydratedCellToken

public export
Eq BiomoduleToken where
  AdenineToken == AdenineToken = True
  ThymineToken == ThymineToken = True
  GuanineToken == GuanineToken = True
  CytosineToken == CytosineToken = True
  HydratedCellToken == HydratedCellToken = True
  _ == _ = False

------------------------------------------------------------------------
-- 6. INDIVIDUAL SCALE TRANSFORMS (T1, T2, T3, T4)
------------------------------------------------------------------------

||| T1: Quark Color Charges -> Hadron Nucleon Tokens
public export
t1_QuarkToHadron : MaxelTransform ColorCharge HadronToken
t1_QuarkToHadron = mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 27)
  [ ((RedColor, ProtonToken), intToBoxInt 1)
  , ((GreenColor, ProtonToken), intToBoxInt 1)
  , ((BlueColor, ProtonToken), intToBoxInt 1)
  ]

||| T1_Full: Full Subatomic Particles (Quarks, Leptons) -> Hadron & Atomic Tokens
public export
t1_SubatomicToHadron : MaxelTransform SubatomicParticle HadronToken
t1_SubatomicToHadron = mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 27)
  [ ((QuarkToken UpQuark, ProtonToken), intToBoxInt 2)
  , ((QuarkToken DownQuark, ProtonToken), intToBoxInt 1)
  , ((QuarkToken UpQuark, NeutronToken), intToBoxInt 1)
  , ((QuarkToken DownQuark, NeutronToken), intToBoxInt 2)
  ]

||| T2: Hadron Nucleon Tokens -> Atomic Element Tokens
public export
t2_HadronToAtom : MaxelTransform HadronToken AtomToken
t2_HadronToAtom = mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 1)
  [ ((ProtonToken, HydrogenToken), intToBoxInt 1)
  , ((NeutronToken, OxygenToken), intToBoxInt 1)
  , ((ProtonToken, HeliumToken), intToBoxInt 2)
  , ((NeutronToken, HeliumToken), intToBoxInt 2)
  ]

||| T3: Atomic Element Tokens -> Molecular Species Tokens
public export
t3_AtomToMolecule : MaxelTransform AtomToken MoleculeToken
t3_AtomToMolecule = mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 1)
  [ ((HydrogenToken, WaterMoleculeToken), intToBoxInt 1)
  , ((OxygenToken, WaterMoleculeToken), intToBoxInt 1)
  , ((CarbonToken, CarbonDioxideToken), intToBoxInt 1)
  , ((OxygenToken, CarbonDioxideToken), intToBoxInt 2)
  ]

||| T4: Molecular Species Tokens -> Cellular Biomodule Tokens
public export
t4_MoleculeToBiomodule : MaxelTransform MoleculeToken BiomoduleToken
t4_MoleculeToBiomodule = mkMaxelTransform EllipticSector (mkUnixelFraction (intToBoxInt 1) 1)
  [ ((WaterMoleculeToken, HydratedCellToken), intToBoxInt 1)
  , ((ATPBioToken, HydratedCellToken), intToBoxInt 1)
  ]

------------------------------------------------------------------------
-- 7. MONOIDAL TRANSFORM COMPOSITION (T_total = T4 ∘ T3 ∘ T2 ∘ T1)
------------------------------------------------------------------------

||| Intermediate T12 = T2 ∘ T1: Quarks -> Atoms
public export
t12_QuarkToAtom : MaxelTransform ColorCharge AtomToken
t12_QuarkToAtom = composeMaxels t1_QuarkToHadron t2_HadronToAtom

||| Intermediate T123 = T3 ∘ T12: Quarks -> Molecules
public export
t123_QuarkToMolecule : MaxelTransform ColorCharge MoleculeToken
t123_QuarkToMolecule = composeMaxels t12_QuarkToAtom t3_AtomToMolecule

||| Composite End-to-End Scale Pipeline Transform T_total = T4 ∘ T3 ∘ T2 ∘ T1: Quarks -> Biomodules
public export
tTotalFunctorialPipeline : MaxelTransform ColorCharge BiomoduleToken
tTotalFunctorialPipeline = composeMaxels t123_QuarkToMolecule t4_MoleculeToBiomodule

------------------------------------------------------------------------
-- 7b. TYPE-SAFE SCALE FUNCTOR REPRESENTATIONS
------------------------------------------------------------------------

||| Type-level ScaleFunctor stage 1: Subatomic -> Hadron
public export
sf1_QuarkToHadron : ScaleFunctor SubatomicLevel HadronLevel ColorCharge HadronToken
sf1_QuarkToHadron = MkScaleFunctor t1_QuarkToHadron

||| Type-level ScaleFunctor stage 2: Hadron -> Atom
public export
sf2_HadronToAtom : ScaleFunctor HadronLevel AtomLevel HadronToken AtomToken
sf2_HadronToAtom = MkScaleFunctor t2_HadronToAtom

||| Type-level ScaleFunctor stage 3: Atom -> Molecule
public export
sf3_AtomToMolecule : ScaleFunctor AtomLevel MoleculeLevel AtomToken MoleculeToken
sf3_AtomToMolecule = MkScaleFunctor t3_AtomToMolecule

||| Type-level ScaleFunctor stage 4: Molecule -> Cell
public export
sf4_MoleculeToBiomodule : ScaleFunctor MoleculeLevel CellLevel MoleculeToken BiomoduleToken
sf4_MoleculeToBiomodule = MkScaleFunctor t4_MoleculeToBiomodule

||| End-to-End Type-Safe ScaleFunctor Pipeline: Subatomic -> Cell
public export
sfTotalFunctorialPipeline : ScaleFunctor SubatomicLevel CellLevel ColorCharge BiomoduleToken
sfTotalFunctorialPipeline = composeScaleFunctors (composeScaleFunctors (composeScaleFunctors sf1_QuarkToHadron sf2_HadronToAtom) sf3_AtomToMolecule) sf4_MoleculeToBiomodule

------------------------------------------------------------------------
-- 8. PIPELINE APPLICATION OPERATOR & INVARIANT AUDIT
------------------------------------------------------------------------

||| Applies the 4-stage consolidated Scale Pipeline in a single pushforward contraction.
public export
applyHierarchicalPipelineContraction : Box ColorCharge -> Box BiomoduleToken
applyHierarchicalPipelineContraction sourceQuarks =
  applyPushforward tTotalFunctorialPipeline sourceQuarks

||| Audits that 9 source quark tokens contract through T_total directly to 9 HydratedCell tokens.
public export
auditFunctorialPipelineProof : Bool
auditFunctorialPipelineProof =
  let source : Box ColorCharge = insertBox RedColor (intToBoxInt 3) (insertBox GreenColor (intToBoxInt 3) (insertBox BlueColor (intToBoxInt 3) emptyBox))
      result = applyHierarchicalPipelineContraction source
  in lookupBox HydratedCellToken result == intToBoxInt 9

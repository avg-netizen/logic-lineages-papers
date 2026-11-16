module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryChooseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryKeyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryAcceptanceWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof ChildInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem applicationForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param typ left right leftKey rightKey leftOut rightOut depRest deps valueRest values : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor (xs 0) typ left right)))
    (hlk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey left (xs 1))))
    (hrk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey right (xs 1))))
    (hlv : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hrv : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta ((graph2 contains (suc z) (xs 2) typ ⊓
      programGraph (fields n) (suc z) (childInputs xs left (xs 1))) ⊓
      programGraph (fields n) (suc z) (childInputs xs right (xs 1)))) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := BinaryKeyProof.applicationDependency key (xs 0) (xs 1) param typ left right leftKey rightKey depRest deps hpair hc hlk hrk hdr hds
  have ha := BinaryInputProof.answers n key param leftKey rightKey depRest deps leftOut rightOut valueRest values hdep hdr hds hlv hrv hvr hvs
  have hfirst := firstValue key param values leftOut valueRest hvs
  have hsecond := BinaryInputProof.secondValue key param values leftOut valueRest rightOut z hvs hvr
  have hrange := Boolean.PointBindingProof.fromValue firstAnswer ![key,values,param] leftOut hfirst
    (Boolean.Proof.extractRange n leftKey param leftOut hlv)
  have hchoose := AcceptanceProof.forward n xs key param values hk hp ha hf
  have hparts := BinaryChooseProof.applicationForward n xs key values param typ left right hk hp hc hrange hchoose
  have hle := valueUnique firstAnswer leftOut (suc z) ![key,values,param] hfirst (andLeft (andRight hparts))
  have hre := valueUnique secondAnswer rightOut (suc z) ![key,values,param] hsecond (andRight (andRight hparts))
  have hlone := outputTransport (extract n) leftOut (suc z) ![leftKey,param] hle hlv
  have hrone := outputTransport (extract n) rightOut (suc z) ![rightKey,param] hre hrv
  exact andIntro (andIntro (andLeft hparts) (fromExtract n xs left (xs 1) leftKey param (suc z) hp hlk hlone))
    (fromExtract n xs right (xs 1) rightKey param (suc z) hp hrk hrone)

theorem applicationBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param typ left right leftKey rightKey leftOut rightOut depRest deps valueRest values : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor (xs 0) typ left right)))
    (hlk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey left (xs 1))))
    (hrk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey right (xs 1))))
    (hlv : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hrv : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) (xs 0))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (hl : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs left (xs 1)))))
    (hr : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs right (xs 1))))) :
    Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := BinaryKeyProof.applicationDependency key (xs 0) (xs 1) param typ left right leftKey rightKey depRest deps hpair hc hlk hrk hdr hds
  have ha := BinaryInputProof.answers n key param leftKey rightKey depRest deps leftOut rightOut valueRest values hdep hdr hds hlv hrv hvr hvs
  have hfirst := firstValue key param values leftOut valueRest hvs
  have hsecond := BinaryInputProof.secondValue key param values leftOut valueRest rightOut z hvs hvr
  have hlone := toExtract n xs left (xs 1) leftKey param (suc z) hp hlk hl
  have hrone := toExtract n xs right (xs 1) rightKey param (suc z) hp hrk hr
  have hle := valueUnique (extract n) leftOut (suc z) ![leftKey,param] hlv hlone
  have hre := valueUnique (extract n) rightOut (suc z) ![rightKey,param] hrv hrone
  have hfone := outputTransport firstAnswer leftOut (suc z) ![key,values,param] hle hfirst
  have hsone := outputTransport secondAnswer rightOut (suc z) ![key,values,param] hre hsecond
  have hchoose := BinaryChooseProof.applicationBackward n xs key values param typ left right hk hp hc hm hfone hsone
  exact AcceptanceProof.backward n xs key param values hk hp ha hg hchoose

theorem consForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param typ left right leftKey rightKey leftOut rightOut depRest deps valueRest values : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor (xs 0) typ left right)))
    (hlk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey left (xs 1))))
    (hrk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey right (xs 1))))
    (hlv : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hrv : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta ((graph2 contains (suc z) (xs 2) typ ⊓
      programGraph (fields n) (suc z) (childInputs xs left (xs 1))) ⊓
      programGraph (fields n) (suc z) (childInputs xs right (xs 1)))) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := BinaryKeyProof.consDependency key (xs 0) (xs 1) param typ left right leftKey rightKey depRest deps hpair hc hlk hrk hdr hds
  have ha := BinaryInputProof.answers n key param leftKey rightKey depRest deps leftOut rightOut valueRest values hdep hdr hds hlv hrv hvr hvs
  have hfirst := firstValue key param values leftOut valueRest hvs
  have hsecond := BinaryInputProof.secondValue key param values leftOut valueRest rightOut z hvs hvr
  have hrange := Boolean.PointBindingProof.fromValue firstAnswer ![key,values,param] leftOut hfirst
    (Boolean.Proof.extractRange n leftKey param leftOut hlv)
  have hchoose := AcceptanceProof.forward n xs key param values hk hp ha hf
  have hparts := BinaryChooseProof.consForward n xs key values param typ left right hk hp hc hrange hchoose
  have hle := valueUnique firstAnswer leftOut (suc z) ![key,values,param] hfirst (andLeft (andRight hparts))
  have hre := valueUnique secondAnswer rightOut (suc z) ![key,values,param] hsecond (andRight (andRight hparts))
  have hlone := outputTransport (extract n) leftOut (suc z) ![leftKey,param] hle hlv
  have hrone := outputTransport (extract n) rightOut (suc z) ![rightKey,param] hre hrv
  exact andIntro (andIntro (andLeft hparts) (fromExtract n xs left (xs 1) leftKey param (suc z) hp hlk hlone))
    (fromExtract n xs right (xs 1) rightKey param (suc z) hp hrk hrone)

theorem consBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param typ left right leftKey rightKey leftOut rightOut depRest deps valueRest values : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor (xs 0) typ left right)))
    (hlk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey left (xs 1))))
    (hrk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey right (xs 1))))
    (hlv : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hrv : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (suc z) (xs 0))))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (hl : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs left (xs 1)))))
    (hr : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs right (xs 1))))) :
    Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := BinaryKeyProof.consDependency key (xs 0) (xs 1) param typ left right leftKey rightKey depRest deps hpair hc hlk hrk hdr hds
  have ha := BinaryInputProof.answers n key param leftKey rightKey depRest deps leftOut rightOut valueRest values hdep hdr hds hlv hrv hvr hvs
  have hfirst := firstValue key param values leftOut valueRest hvs
  have hsecond := BinaryInputProof.secondValue key param values leftOut valueRest rightOut z hvs hvr
  have hlone := toExtract n xs left (xs 1) leftKey param (suc z) hp hlk hl
  have hrone := toExtract n xs right (xs 1) rightKey param (suc z) hp hrk hr
  have hle := valueUnique (extract n) leftOut (suc z) ![leftKey,param] hlv hlone
  have hre := valueUnique (extract n) rightOut (suc z) ![rightKey,param] hrv hrone
  have hfone := outputTransport firstAnswer leftOut (suc z) ![key,values,param] hle hfirst
  have hsone := outputTransport secondAnswer rightOut (suc z) ![key,values,param] hre hsecond
  have hchoose := BinaryChooseProof.consBackward n xs key values param typ left right hk hp hc hm hfone hsone
  exact AcceptanceProof.backward n xs key param values hk hp ha hg hchoose
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryAcceptanceWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryAcceptanceWitnessProof

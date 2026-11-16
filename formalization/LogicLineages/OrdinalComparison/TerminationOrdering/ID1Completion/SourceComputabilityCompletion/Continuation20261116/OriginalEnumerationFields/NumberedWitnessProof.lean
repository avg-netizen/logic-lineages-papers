module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedChooseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryAcceptanceWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedWitnessProof
open Continuation20261115
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

theorem forward (n : Nat) (xs : Fin 6 → OTerm alpha)
    (key param label head typ base list extra leftKey rightKey leftOut rightOut depRest deps valueRest values mapped len : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,list,extra])))
    (hlk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey base (xs 1))))
    (hrk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey extra (xs 1))))
    (hlv : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hrv : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta (((((InternalLessThan.strictLess label (suc (xs 4)) ⊓ Targets.headAllowed n (xs 3) head) ⊓
      graph2 contains (suc z) (xs 2) typ) ⊓ programGraph (fields n) (suc z) (childInputs xs base (xs 1))) ⊓
      Targets.typesAllowed list (xs 2) (xs 5)) ⊓ programGraph (fields n) (suc z) (childInputs xs extra (xs 1)))) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := BinaryKeyProof.numberedDependency key (xs 0) (xs 1) param label head typ base list extra
    leftKey rightKey depRest deps hpair hc hlk hrk hdr hds
  have ha := BinaryInputProof.answers n key param leftKey rightKey depRest deps leftOut rightOut valueRest values hdep hdr hds hlv hrv hvr hvs
  have hfirst := firstValue key param values leftOut valueRest hvs
  have hsecond := BinaryInputProof.secondValue key param values leftOut valueRest rightOut z hvs hvr
  have hrange := Boolean.PointBindingProof.fromValue firstAnswer ![key,values,param] leftOut hfirst
    (Boolean.Proof.extractRange n leftKey param leftOut hlv)
  have hchoose := AcceptanceProof.forward n xs key param values hk hp ha hf
  have hparts := NumberedChooseProof.forward n xs key values param label head typ base list extra mapped len hk hp hc hmap hlen hrange hchoose
  have hs := andRight hparts
  have t4 := andLeft hparts
  have ht := andRight t4
  have t3 := andLeft t4
  have hb := andRight t3
  have t2 := andLeft t3
  have hle := valueUnique firstAnswer leftOut (suc z) ![key,values,param] hfirst hb
  have hre := valueUnique secondAnswer rightOut (suc z) ![key,values,param] hsecond hs
  have hlone := outputTransport (extract n) leftOut (suc z) ![leftKey,param] hle hlv
  have hrone := outputTransport (extract n) rightOut (suc z) ![rightKey,param] hre hrv
  exact andIntro (andIntro (andIntro t2 (fromExtract n xs base (xs 1) leftKey param (suc z) hp hlk hlone)) ht)
    (fromExtract n xs extra (xs 1) rightKey param (suc z) hp hrk hrone)

theorem backward (n : Nat) (xs : Fin 6 → OTerm alpha)
    (key param label head typ base list extra leftKey rightKey leftOut rightOut depRest deps valueRest values mapped len : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,list,extra])))
    (hlk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftKey base (xs 1))))
    (hrk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightKey extra (xs 1))))
    (hlv : Nonempty (Derivation body Delta (graph2 (extract n) leftOut leftKey param)))
    (hrv : Nonempty (Derivation body Delta (graph2 (extract n) rightOut rightKey param)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depRest rightKey z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps leftKey depRest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rightOut z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values leftOut valueRest)))
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0))))
    (h0 : Nonempty (Derivation body Delta (InternalLessThan.strictLess label (suc (xs 4)))))
    (h1 : Nonempty (Derivation body Delta (Targets.headAllowed n (xs 3) head)))
    (h2 : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (h3 : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs base (xs 1)))))
    (h4 : Nonempty (Derivation body Delta (Targets.typesAllowed list (xs 2) (xs 5))))
    (h5 : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) (childInputs xs extra (xs 1))))) :
    Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hdep := BinaryKeyProof.numberedDependency key (xs 0) (xs 1) param label head typ base list extra
    leftKey rightKey depRest deps hpair hc hlk hrk hdr hds
  have ha := BinaryInputProof.answers n key param leftKey rightKey depRest deps leftOut rightOut valueRest values hdep hdr hds hlv hrv hvr hvs
  have hfirst := firstValue key param values leftOut valueRest hvs
  have hsecond := BinaryInputProof.secondValue key param values leftOut valueRest rightOut z hvs hvr
  have hlone := toExtract n xs base (xs 1) leftKey param (suc z) hp hlk h3
  have hrone := toExtract n xs extra (xs 1) rightKey param (suc z) hp hrk h5
  have hle := valueUnique (extract n) leftOut (suc z) ![leftKey,param] hlv hlone
  have hre := valueUnique (extract n) rightOut (suc z) ![rightKey,param] hrv hrone
  have hfone := outputTransport firstAnswer leftOut (suc z) ![key,values,param] hle hfirst
  have hsone := outputTransport secondAnswer rightOut (suc z) ![key,values,param] hre hsecond
  have hchoose := NumberedChooseProof.backward n xs key values param label head typ base list extra mapped len hk hp hc hmap hlen
    h0 h1 h2 hfone h4 hsone
  exact AcceptanceProof.backward n xs key param values hk hp ha hg hchoose
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedWitnessProof

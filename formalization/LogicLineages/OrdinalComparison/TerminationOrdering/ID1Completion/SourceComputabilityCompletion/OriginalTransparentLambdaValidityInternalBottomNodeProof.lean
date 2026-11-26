module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomNodeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBottomShapeProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBranchSupportProof OriginalTransparentLambdaValidityInternalBranchValueProof
open OriginalTransparentLambdaValidityInternalSourceCheckProof (sourceCheck)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem sourceBottomRecover (rawData : Data) (raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw)))
    (hn : Nonempty (Derivation body Gamma
      (NodeFactors (sourceRoot (normalizedData rawData)) (targetRoot (normalizedData rawData))
        (normalizedData rawData).member raw parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 rawData.oldSource (numeral 1) raw contextOnly ⊓
        graph2 rawData.oldTarget (numeral 1) raw contextOnly)) := by
  let N := normalizedData rawData
  have h2 := bottomNotTwo raw hb
  have h1 := bottomNotOne raw hb
  have hs := dispatchOpaque N.oldSource (sourceCheck N) (numeral 1) raw parameter h2 h1 (andLeft hn)
  have ht := dispatchOpaque N.oldTarget lambdaShape (numeral 1) raw parameter h2 h1 (andLeft (andRight hn))
  exact andIntro
    (BottomParameterInternalProof.normalizedRecover rawData.oldSource (numeral 1)
      raw parameter context gammaCode contextOnly hp hz hb hs)
    (BottomParameterInternalProof.normalizedRecover rawData.oldTarget (numeral 1)
      raw parameter context gammaCode contextOnly hp hz hb ht)

theorem sourceBottomValue (rawData : Data) (raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw)))
    (hf : Nonempty (Derivation body Gamma
      (graph2 rawData.oldSource (numeral 1) raw contextOnly ⊓
        graph2 rawData.oldTarget (numeral 1) raw contextOnly))) :
    Nonempty (Derivation body Gamma
      (NodeFactors (sourceRoot (normalizedData rawData)) (targetRoot (normalizedData rawData))
        (normalizedData rawData).member raw parameter)) := by
  let N := normalizedData rawData
  have h2 := bottomNotTwo raw hb
  have h1 := bottomNotOne raw hb
  have hs := BottomParameterInternalProof.normalizedValue rawData.oldSource (numeral 1)
    raw parameter context gammaCode contextOnly hp hz hb (andLeft hf)
  have ht := BottomParameterInternalProof.normalizedValue rawData.oldTarget (numeral 1)
    raw parameter context gammaCode contextOnly hp hz hb (andRight hf)
  exact nodeAtThree (sourceRoot N) (targetRoot N) N.member raw parameter
    (dispatchOpaqueValue N.oldSource (sourceCheck N) (numeral 1) raw parameter h2 h1 hs)
    (dispatchOpaqueValue N.oldTarget lambdaShape (numeral 1) raw parameter h2 h1 ht) (bottomTag raw hb)

theorem sourceBottomNodeEquation (rawData : Data) (raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors (sourceRoot (normalizedData rawData)) (targetRoot (normalizedData rawData))
        (normalizedData rawData).member raw parameter).iff
          (graph2 rawData.oldSource (numeral 1) raw contextOnly ⊓
            graph2 rawData.oldTarget (numeral 1) raw contextOnly))) := by
  let N := normalizedData rawData
  let A := NodeFactors (sourceRoot N) (targetRoot N) N.member raw parameter
  let B := graph2 rawData.oldSource (numeral 1) raw contextOnly ⊓
    graph2 rawData.oldTarget (numeral 1) raw contextOnly
  obtain ⟨hf⟩ := sourceBottomRecover rawData raw parameter context gammaCode contextOnly
    (addAssumption hp A) (addAssumption hz A) (addAssumption hb A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hr⟩ := sourceBottomValue rawData raw parameter context gammaCode contextOnly
    (addAssumption hp B) (addAssumption hz B) (addAssumption hb B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hr)⟩

theorem targetBottomRecover (rawData : Data) (raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw)))
    (hn : Nonempty (Derivation body Gamma
      (NodeFactors (targetRoot (normalizedData rawData)) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 rawData.oldTarget (numeral 1) raw contextOnly)) := by
  let N := normalizedData rawData
  have ht := dispatchOpaque N.oldTarget lambdaShape (numeral 1) raw parameter
    (bottomNotTwo raw hb) (bottomNotOne raw hb) (andLeft hn)
  exact BottomParameterInternalProof.normalizedRecover rawData.oldTarget (numeral 1)
    raw parameter context gammaCode contextOnly hp hz hb ht

theorem targetBottomValue (rawData : Data) (raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw)))
    (hf : Nonempty (Derivation body Gamma (graph2 rawData.oldTarget (numeral 1) raw contextOnly))) :
    Nonempty (Derivation body Gamma
      (NodeFactors (targetRoot (normalizedData rawData)) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter)) := by
  let N := normalizedData rawData
  have ht := BottomParameterInternalProof.normalizedValue rawData.oldTarget (numeral 1)
    raw parameter context gammaCode contextOnly hp hz hb hf
  exact nodeAtThree (targetRoot N) (InternalLessThan.constantOne 2) (InternalLessThan.constantOne 2)
    raw parameter (dispatchOpaqueValue N.oldTarget lambdaShape (numeral 1) raw parameter
      (bottomNotTwo raw hb) (bottomNotOne raw hb) ht)
    (InternalLessThanSupportProof.oneConstantValue (Fin.cons raw (Fin.cons parameter Fin.elim0))) (bottomTag raw hb)

theorem targetBottomNodeEquation (rawData : Data) (raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors (targetRoot (normalizedData rawData)) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter).iff
          (graph2 rawData.oldTarget (numeral 1) raw contextOnly))) := by
  let N := normalizedData rawData
  let A := NodeFactors (targetRoot N) (InternalLessThan.constantOne 2) (InternalLessThan.constantOne 2) raw parameter
  let B := graph2 rawData.oldTarget (numeral 1) raw contextOnly
  obtain ⟨hf⟩ := targetBottomRecover rawData raw parameter context gammaCode contextOnly
    (addAssumption hp A) (addAssumption hz A) (addAssumption hb A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hr⟩ := targetBottomValue rawData raw parameter context gammaCode contextOnly
    (addAssumption hp B) (addAssumption hz B) (addAssumption hb B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hr)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomNodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomNodeProof

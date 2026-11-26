module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomNodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomParameterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open InternalOriginalUniformDescentSelection (Data)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBottomNodeProof OriginalTransparentLambdaValidityInternalBottomOutputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem iffVia (A B F : Formula alpha)
    (hA : Nonempty (Derivation body Gamma (A.iff F)))
    (hB : Nonempty (Derivation body Gamma (B.iff F))) :
    Nonempty (Derivation body Gamma (A.iff B)) := by
  obtain ⟨hA⟩ := hA
  obtain ⟨hB⟩ := hB
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight hB) A)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hA) A)
        (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight hA) B)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hB) B)
        (Derivation.hypothesis List.mem_cons_self))))⟩

theorem sourceBottomParameter (rawData : Data) (out raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (sourceValidator rawData) out raw parameter).iff
        (graph2 (sourceValidator rawData) out raw contextOnly))) := by
  let N := normalizedData rawData
  let F := graph2 rawData.oldSource (numeral 1) raw contextOnly ⊓
    graph2 rawData.oldTarget (numeral 1) raw contextOnly
  exact iffVia _ _ (BooleanOutput out F)
    (bottomOutputEquation (sourceRoot N) (targetRoot N) N.member out raw parameter F hb
      (sourceBottomNodeEquation rawData raw parameter context gammaCode contextOnly hp hz hb))
    (bottomOutputEquation (sourceRoot N) (targetRoot N) N.member out raw contextOnly F hb
      (sourceBottomNodeEquation rawData raw contextOnly context z contextOnly hz hz hb))

theorem targetBottomParameter (rawData : Data) (out raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetValidator rawData) out raw parameter).iff
        (graph2 (targetValidator rawData) out raw contextOnly))) := by
  let N := normalizedData rawData
  let F := graph2 rawData.oldTarget (numeral 1) raw contextOnly
  exact iffVia _ _ (BooleanOutput out F)
    (bottomOutputEquation (targetRoot N) (InternalLessThan.constantOne 2) (InternalLessThan.constantOne 2)
      out raw parameter F hb (targetBottomNodeEquation rawData raw parameter context gammaCode contextOnly hp hz hb))
    (bottomOutputEquation (targetRoot N) (InternalLessThan.constantOne 2) (InternalLessThan.constantOne 2)
      out raw contextOnly F hb (targetBottomNodeEquation rawData raw contextOnly context z contextOnly hz hz hb))

theorem actualOriginalTransparentInternalBottomParameter :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalBottomParameter := by
  intro body rawData alpha out raw parameter context encodedGamma contextOnly
  let A := graph2 InternalPairing.pairing parameter context encodedGamma ⊓
    (graph2 InternalPairing.pairing contextOnly context z ⊓ BottomRepresentative.bottomGraph (numeral 1) raw)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hs⟩ := sourceBottomParameter rawData out raw parameter context encodedGamma contextOnly
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  obtain ⟨ht⟩ := targetBottomParameter rawData out raw parameter context encodedGamma contextOnly
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hs ht)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomParameterProof

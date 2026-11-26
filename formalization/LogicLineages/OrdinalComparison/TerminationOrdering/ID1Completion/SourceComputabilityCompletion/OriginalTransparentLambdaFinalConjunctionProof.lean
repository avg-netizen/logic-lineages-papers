module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalConjunctionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaFinal OriginalTransparentLambdaFinalLogicProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem conjunctionAcceptance {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((programGraph (InternalAcceptance.conjunction p q) (numeral 1) xs).iff
        (programGraph p (numeral 1) xs ⊓ programGraph q (numeral 1) xs))) := by
  let A := programGraph (InternalAcceptance.conjunction p q) (numeral 1) xs
  let B := programGraph p (numeral 1) xs ⊓ programGraph q (numeral 1) xs
  obtain ⟨hf⟩ := conjunctionRecover (body := body) (Gamma := A :: Gamma) p q xs
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hb : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := conjunctionAccept p q xs (andLeft hb) (andRight hb)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- Combine independently proved exact target and universe graph laws.
Both sides remain the original exact-one conjunction ASTs on every output. -/
theorem sourceCollapse (rawData selected : Data)
    (ht : TargetCollapse rawData selected) (hs : UniverseCollapse rawData selected) :
    SourceCollapse rawData selected := by
  intro body alpha Delta out raw parameter
  let T := InternalOriginalUniformDescentSelection.targetValidity selected
  let U := InternalParameterizedApplicationValidityFold.universeP selected.oldSource selected.member
  let HT := OriginalTransparentLambdaValidity.targetValidator rawData
  let HS := OriginalTransparentLambdaValidity.sourceValidator rawData
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  exact iffCompose (conjunctionEquation T U xs out)
    (iffCompose
      (booleanIff out (andIff (ht body alpha Delta (numeral 1) raw parameter)
        (hs body alpha Delta (numeral 1) raw parameter)))
      (iffReverse (conjunctionEquation HT HS xs out)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalConjunctionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalConjunctionProof

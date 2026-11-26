module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalAcceptanceNormalizationProof
open InternalBetaTotalityProof (addHyp)
open OriginalTransparentLambdaValidityInternalBooleanProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
open OriginalTransparentLambdaValidityInternalNormalizationProof
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Exact-one normalization preserves a Boolean validator after any already
proved full-output leaf transport. No numerical evaluation is reflected. -/
theorem normalizedLeafEquation (old s t m : Program 2)
    (raw parameter : OTerm alpha)
    (transport : ∀ (Delta : List (Formula alpha)) (o : OTerm alpha),
      Nonempty (Derivation body Delta
        ((graph2 old o raw parameter).iff (graph2 (validator s t m) o raw parameter))))
    (out : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (GorbowVerifierNormalization.normalize old) out raw parameter).iff
        (graph2 (validator s t m) out raw parameter))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hy : Nonempty (Derivation body Gamma
      (A.imp (graph2 (GorbowVerifierNormalization.normalize old) (numeral 1) raw parameter))) := by
    obtain ⟨he⟩ := transport (A :: Gamma) (numeral 1)
    obtain ⟨hn⟩ := normalizeAccept old xs
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight he)
        (Derivation.hypothesis List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction hn⟩
  have hn : Nonempty (Derivation body Gamma
      (A.not.imp (graph2 (GorbowVerifierNormalization.normalize old) z raw parameter))) := by
    let B := graph2 old (numeral 1) raw parameter
    obtain ⟨he⟩ := transport (B :: A.not :: Gamma) (numeral 1)
    have hb : Nonempty (Derivation body (A.not :: Gamma) B.not) :=
      ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.implicationElimination (Derivation.conjunctionLeft he)
          (Derivation.hypothesis List.mem_cons_self)))⟩
    obtain ⟨hz⟩ := normalizeReject old xs hb
    exact ⟨Derivation.implicationIntroduction hz⟩
  obtain ⟨hleft⟩ := booleanEquation (GorbowVerifierNormalization.normalize old) xs out A hy hn
  have vy : Nonempty (Derivation body Gamma (A.imp A)) :=
    ⟨Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)⟩
  have vn : Nonempty (Derivation body Gamma
      (A.not.imp (graph2 (validator s t m) z raw parameter))) := by
    obtain ⟨hz⟩ := validatorReject s t m raw parameter
      (show Nonempty (Derivation body (A.not :: Gamma) A.not) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction hz⟩
  obtain ⟨hright⟩ := booleanEquation (validator s t m) xs out A vy vn
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight hright) _)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hleft) _)
        (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight hleft) _)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hright) _)
        (Derivation.hypothesis List.mem_cons_self))))⟩

theorem sourceLeafEquation (data : InternalOriginalUniformDescentSelection.Data)
    (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalParameterizedApplicationValidityFold.leafP
        (BottomParameter.normalized (sourceValidator data))) out raw parameter).iff
        (graph2 (sourceValidator data) out raw parameter))) := by
  apply normalizedLeafEquation
  intro Delta o
  obtain ⟨h⟩ := (actualOriginalTransparentInternalBottomNormalization body data alpha o raw parameter).1
  exact OriginalHereditaryValidityInternalNodeSupportProof.weakenProof ⟨h⟩ (by intro p hp; cases hp)

theorem targetLeafEquation (data : InternalOriginalUniformDescentSelection.Data)
    (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalParameterizedApplicationValidityFold.leafP
        (BottomParameter.normalized (targetValidator data))) out raw parameter).iff
        (graph2 (targetValidator data) out raw parameter))) := by
  apply normalizedLeafEquation
  intro Delta o
  obtain ⟨h⟩ := (actualOriginalTransparentInternalBottomNormalization body data alpha o raw parameter).2
  exact OriginalHereditaryValidityInternalNodeSupportProof.weakenProof ⟨h⟩ (by intro p hp; cases hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLeafProof

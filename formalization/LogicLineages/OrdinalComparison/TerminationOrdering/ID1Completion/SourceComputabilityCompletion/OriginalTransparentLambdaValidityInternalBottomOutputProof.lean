module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrencePopProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalRecurrenceAcceptanceProof (acceptanceFactors)
open OriginalHereditaryValidityInternalRecurrenceOutputSupportProof (validatorReject)
open OriginalHereditaryValidityInternalRecurrencePopProof (popRecurrence)
open OriginalTransparentLambdaValidityInternal OriginalTransparentLambdaValidityInternalBooleanProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBottomShapeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem bottomAcceptanceEquation (s t m : Program 2) (raw parameter : OTerm alpha)
    (F : Formula alpha)
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw)))
    (hnode : Nonempty (Derivation body Gamma ((NodeFactors s t m raw parameter).iff F))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff F)) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  have hf : Nonempty (Derivation body (A :: Gamma) F) := by
    have ha : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hn⟩ := acceptanceFactors s t m raw parameter ha
    obtain ⟨hnode'⟩ := addAssumption hnode A
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hnode') hn⟩
  have hr : Nonempty (Derivation body (F :: Gamma) A) := by
    obtain ⟨hnode'⟩ := addAssumption hnode F
    have hn : Nonempty (Derivation body (F :: Gamma) (NodeFactors s t m raw parameter)) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hnode')
        (Derivation.hypothesis List.mem_cons_self)⟩
    exact popRecurrence s t m raw parameter (numeral 3) hn
      (bottomTag raw (addAssumption hb F)) threeNeTwo threeNeOne
  obtain ⟨hf⟩ := hf
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hr)⟩

theorem bottomOutputEquation (s t m : Program 2) (out raw parameter : OTerm alpha)
    (F : Formula alpha)
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw)))
    (hnode : Nonempty (Derivation body Gamma ((NodeFactors s t m raw parameter).iff F))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) out raw parameter).iff (BooleanOutput out F))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  obtain ⟨he⟩ := bottomAcceptanceEquation s t m raw parameter F hb hnode
  have hy : Nonempty (Derivation body Gamma (F.imp A)) := ⟨Derivation.conjunctionRight he⟩
  have hn : Nonempty (Derivation body Gamma
      (F.not.imp (graph2 (validator s t m) z raw parameter))) := by
    have hna : Nonempty (Derivation body (F.not :: Gamma) A.not) :=
      ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.implicationElimination (addHyp (addHyp (Derivation.conjunctionLeft he) F.not) A)
          (Derivation.hypothesis List.mem_cons_self)))⟩
    obtain ⟨hz⟩ := validatorReject s t m raw parameter hna
    exact ⟨Derivation.implicationIntroduction hz⟩
  exact booleanEquation (validator s t m) (Fin.cons raw (Fin.cons parameter Fin.elim0)) out F hy hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomOutputProof

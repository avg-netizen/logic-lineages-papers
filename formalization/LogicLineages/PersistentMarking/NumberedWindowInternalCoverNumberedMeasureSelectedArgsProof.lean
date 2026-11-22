module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename moveReport)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverLambdaSelectedMeasurePairCasesProof (codePairCases)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets (numberedJoin)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualArgsPairCases (A : Program 1) (arg : OTerm α) (Q : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m d w : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary (selectedArgsMeasure A) m (arg.relabel j))) →
      Nonempty (Derivation body Δ (codePair m d w)) →
      Nonempty (Derivation body Δ (Q.relabel j))) : Nonempty (Derivation body Γ Q) := by
  apply programCases (selectedArgsMeasure A) ![arg] Q
  intro β j Δ m keep observed
  rw [inputsRename] at observed
  apply codePairCases m (Q.relabel j)
  intro γ k Ξ d w retain paired
  have both : ∀ f ∈ Γ, f.relabel (k ∘ j) ∈ Ξ := by
    intro f hf
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  have args := moveReport k Ξ retain (selectedArgsMeasure A) m (arg.relabel j) observed
  simp only [Term.relabel_relabel] at args
  rw [formulaRelabelComposition j k Q]
  exact next γ (k ∘ j) Ξ (m.relabel k) d w both args paired

private theorem selectedField (A : Program 1) (i : Nat) (raw arg m : OTerm α)
    (parse : Nonempty (Derivation body Γ (unary (field i) arg raw)))
    (measured : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) m arg))) :
    Nonempty (Derivation body Γ (unary (numberedArgCode A i) m raw)) := by
  apply compositionValue (selectedArgsMeasure A) (fun _ : Fin 1 => field i) m ![raw] ![arg] measured
  intro j
  obtain rfl := Fin.eq_zero j
  exact parse

theorem exact_OpenNumberedJoinFromFields (A : Program 1) (h ty k l r p ml mr : OTerm α)
    (cut : Nonempty (Derivation body Γ (unary (numberedMeasureApply A) p (numberedTerm h ty k l r))))
    (left : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) ml l)))
    (right : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) mr r))) :
    Nonempty (Derivation body Γ (programGraph numberedJoin p ![k,ml,mr])) := by
  let raw := numberedTerm h ty k l r
  have tag : Nonempty (Derivation body Γ (unary (literal 1 5) (numeral 5) raw)) :=
    literalGraph 5 ![raw]
  have reads := (packedNode (literal 1 5) (numeral 5) [h,ty,k,l,r] tag).2
  apply compositionRecover numberedJoin ![field 2,numberedArgCode A 3,numberedArgCode A 4]
    p ![raw] ![k,ml,mr] cut
  intro j
  exact Fin.cases reads.2.2.1
    (Fin.cases (selectedField A 3 raw l ml reads.2.2.2.1 left)
      (Fin.cases (selectedField A 4 raw r mr reads.2.2.2.2.1 right) (fun i => Fin.elim0 i))) j

#print axioms actualArgsPairCases
#print axioms exact_OpenNumberedJoinFromFields

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof

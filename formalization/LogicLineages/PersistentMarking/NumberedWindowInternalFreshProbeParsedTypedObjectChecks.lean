module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedResultProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedLiteralSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalProbeTargets (OTerm typedAt)
open NumberedWindowInternalFreshProbeDispatchObjectChecks (exact_ProbeTypedTotal)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (typedRename)
open NumberedWindowInternalFreshProbeParsedEmitterObjectChecks (exact_OpenParsedFresh)
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets
open NumberedWindowInternalFreshProbeParsedTypedResultProof (openResult)
open NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof (actualArrowFields)
open NumberedWindowInternalFreshProbeParsedTypedLiteralSyntaxProof

theorem exact_OpenRequestedResultField : ExactOpenRequestedResultField := openResult

theorem exact_OpenLiteralParsedFresh : ExactOpenLiteralParsedFresh := by
  intro i W σ τ body α Γ q u ht ha
  have hp := exact_OpenParsedFresh i.scalarProg i.freshBound body α Γ q u ha
  rw [rawBlock] at hp
  apply actualFiniteExistentialElimination body α 6 Γ (rawMatrix i.freshBound q u)
    (literalParsedAt i.freshBound σ τ q u) hp
  let j : α → α ⊕ Fin 6 := Sum.inl
  let Δ : List (Formula (α ⊕ Fin 6)) := rawMatrix i.freshBound q u :: Γ.map (fun f => f.relabel j)
  let y : Fin 6 → OTerm (α ⊕ Fin 6) := fun k => .var (.inr k)
  let q' := q.relabel j
  let u' := u.relabel j
  have inc : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have htype := renameInto ht j Δ inc
  rw [typedRename] at htype
  have raw : Derivation body Δ (rawFactors i.freshBound q' u' (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)) :=
    Derivation.hypothesis List.mem_cons_self
  have address := Derivation.conjunctionLeft raw
  have reportedResult := Derivation.conjunctionLeft (Derivation.conjunctionRight address)
  have shape := Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight raw))
  have rawArrow := Derivation.conjunctionRight shape
  have actualResult := openResult i W (.arrow σ τ) body _ Δ q' (y 1) htype ⟨reportedResult⟩
  have components := actualArrowFields σ τ (y 1) (y 2) (y 3) actualResult ⟨rawArrow⟩
  rw [literalRename]
  exact literalIntro i.freshBound σ τ q' u' y ⟨raw⟩ components

theorem exact_SameParsedTypedProbeTotal : ExactSameParsedTypedProbeTotal := by
  intro i W closed d c
  exact exact_ProbeTypedTotal (chosenLeaves i) W closed d c

#print axioms exact_OpenRequestedResultField
#print axioms exact_OpenLiteralParsedFresh
#print axioms exact_SameParsedTypedProbeTotal
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks

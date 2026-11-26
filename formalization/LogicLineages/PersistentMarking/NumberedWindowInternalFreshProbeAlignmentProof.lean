module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source (Ty)
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalProbeTargets (OTerm typedAt freshAt witnesses)
open NumberedWindowInternalFreshProbeChecks (exact_FreshProbeUnique)
open NumberedWindowInternalFreshProbeSyntaxProof (freshRename)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (alignedRename resultIntro)
open NumberedWindowInternalFreshProbeAlignmentTargets

/-- Transport only the second actual program input. The source and
result positions use internal reflexivity rather than new witnesses. -/
private theorem moveArgument {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Program 3) (q old given v : OTerm α)
    (he : Nonempty (Derivation body Γ (equal old given)))
    (ha : Nonempty (Derivation body Γ (accepts p q old v))) :
    Nonempty (Derivation body Γ (accepts p q given v)) := by
  have self (t : OTerm α) : Nonempty (Derivation body Γ (equal t t)) := by
    rw [equalEqn]
    exact ⟨refl t⟩
  apply graphInputTransport body α 3 Γ (OrdinaryArithmetic.graphFormula p) (suc z)
    ![q,old,v] ![q,given,v] _ ha
  intro k
  exact Fin.cases (self q) (Fin.cases he (Fin.cases (self v) (fun i => Fin.elim0 i))) k

private theorem carry {α : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    {A : Formula α} (H : Formula (α ⊕ Fin 1)) (d : Nonempty (Derivation body Γ A)) :
    Nonempty (Derivation body (H :: Γ.map weaken) (A.relabel (Sum.inl : α → α ⊕ Fin 1))) :=
  renameInto d Sum.inl _ (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))

theorem align : ExactGivenFreshProbeAlignment := by
  intro d p h a c total σ τ α Γ q u ht hf
  obtain ⟨ex⟩ := total σ τ α Γ q ht
  let q' := q.relabel (Sum.inl : α → α ⊕ Fin 1)
  let q'' := q'.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let u' := u.relabel (Sum.inl : α → α ⊕ Fin 1)
  let u'' := u'.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let selected : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let v : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let A := freshAt a q'' selected ⊓ (accepts p q'' selected v ⊓ typedAt h τ v)
  let E := existsOne A
  let Δ := E :: Γ.map weaken
  let Θ := A :: Δ.map weaken
  have actual : Derivation (sourceBody d c) Θ A := Derivation.hypothesis List.mem_cons_self
  have given := carry A (carry E hf)
  rw [freshRename,freshRename] at given
  have first : Nonempty (Derivation (sourceBody d c) Θ
      (freshAt a q'' selected ⊓ freshAt a q'' u'')) := by
    obtain ⟨hGiven⟩ := given
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft actual) hGiven⟩
  have he := closedApply
    (exact_FreshProbeUnique (sourceBody d c) a _ [] q'' selected u'') first
  have rest := Derivation.conjunctionRight actual
  have app := moveArgument p q'' selected u'' v he ⟨Derivation.conjunctionLeft rest⟩
  obtain ⟨result⟩ := resultIntro p h τ q'' u'' v app ⟨Derivation.conjunctionRight rest⟩
  apply Nonempty.intro
  apply Derivation.existentialElimination ex
  change Derivation _ Δ ((alignedResultAt p h τ q u).relabel Sum.inl)
  rw [alignedRename]
  apply Derivation.existentialElimination (Derivation.hypothesis (List.mem_cons_self : E ∈ Δ))
  change Derivation _ Θ ((alignedResultAt p h τ q' u').relabel Sum.inl)
  rw [alignedRename]
  exact result

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentProof

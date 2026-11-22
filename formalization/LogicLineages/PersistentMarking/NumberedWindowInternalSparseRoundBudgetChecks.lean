module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.SourceComputabilityCompletion
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseRoundReachChecks (exact_AdjacentRoundPersistence)
open NumberedWindowInternalSparseRoundsInclusionChecks (exact_RoundsInclusionFromPass)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalSparseRoundBudgetTargets

theorem exact_BudgetPrograms : ExactBudgetPrograms := ⟨rfl,rfl⟩

private theorem memberFormula {α : Type} (pool k : OTerm α) :
    graph2 contains (numeral 1) pool k = memberGraph pool k := by
  unfold graph2 memberGraph
  congr 1

theorem exact_BudgetInclusion : ExactBudgetInclusion := by
  intro E body α Γ before after fuel vertices ctx ty seed
  let A := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have incl : Nonempty (Derivation body Δ (PrimaryMonotonicity.included before after)) := by
    apply ID1Completion.InternalClosedProgramsBindingProof.introduction body α 1 Δ
    let j : α → α ⊕ Fin 1 := Sum.inl
    let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    let M := graph2 contains (numeral 1) (before.relabel j) k
    let Θ := M :: Δ.map weaken
    have keep (p : Formula α) (hp : p ∈ Δ) : p.relabel j ∈ Θ :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
    have prev := renameInto ⟨Derivation.conjunctionLeft h⟩ j Θ keep
    have next := renameInto ⟨Derivation.conjunctionRight h⟩ j Θ keep
    rw [roundRename] at prev
    rw [roundRename,sucRelabel] at next
    obtain ⟨prev⟩ := prev
    obtain ⟨next⟩ := next
    obtain ⟨carry⟩ := exact_AdjacentRoundPersistence E body _ Θ (before.relabel j) (after.relabel j)
      (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) k
    have present : Derivation body Θ (memberGraph (before.relabel j) k) := by
      rw [← memberFormula]
      exact Derivation.hypothesis List.mem_cons_self
    have out := Derivation.implicationElimination carry
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction prev next) present)
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    change Derivation body Θ (graph2 contains (numeral 1) (after.relabel j) k)
    rwa [memberFormula]
  obtain ⟨incl⟩ := incl
  exact ⟨Derivation.implicationIntroduction incl⟩

theorem exact_NewMemberDecrease : ExactNewMemberDecrease := by
  intro strict E body α Γ before after fuel vertices ctx ty seed beforeCount afterCount k
  let stages := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let counts := graph2 PrimaryUncoveredCount.count beforeCount vertices before ⊓
    graph2 PrimaryUncoveredCount.count afterCount vertices after
  let fresh := (memberGraph before k).not ⊓ memberGraph after k
  let A := stages ⊓ (counts ⊓ fresh)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have both := Derivation.conjunctionLeft h
  have rest := Derivation.conjunctionRight h
  have values := Derivation.conjunctionLeft rest
  have hits := Derivation.conjunctionRight rest
  have hk := Derivation.conjunctionRight hits
  obtain ⟨inc⟩ := exact_BudgetInclusion E body α Δ before after fuel vertices ctx ty seed
  have subset := (exact_RoundsInclusionFromPass E (exact_DirectedPassInclusion (constantZero 4))
    (exact_DirectedPassInclusion E)).1
  obtain ⟨law⟩ := subset body α Δ after (suc fuel) vertices ctx ty seed k
  have vertex := Derivation.implicationElimination law (Derivation.conjunctionIntroduction (Derivation.conjunctionRight both) hk)
  obtain ⟨drop⟩ := strict body α Δ vertices before after beforeCount afterCount k
    ⟨Derivation.implicationElimination inc both⟩ ⟨Derivation.conjunctionLeft values⟩ ⟨Derivation.conjunctionRight values⟩
    (by rw [memberFormula]; exact ⟨vertex⟩) (by rw [memberFormula]; exact ⟨Derivation.conjunctionLeft hits⟩)
    (by rw [memberFormula]; exact ⟨hk⟩)
  exact ⟨Derivation.implicationIntroduction drop⟩

#print axioms exact_BudgetPrograms
#print axioms exact_BudgetInclusion
#print axioms exact_NewMemberDecrease
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetChecks

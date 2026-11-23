module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundBudgetTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundBudgetChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseRoundReachChecks (exact_AdjacentRoundPersistence)
open NumberedWindowInternalSparseRoundsInclusionChecks (exact_RoundsInclusionFromPass)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalThinRoundBudgetTargets

private theorem memberFormula {α : Type} (pool k : OTerm α) :
    graph2 NumberedWindowInternalSparseScratchMembership.scratchMember (numeral 1) pool k =
      memberGraph pool k := by
  unfold graph2 memberGraph
  congr 1

theorem exact_BudgetInclusion : ExactBudgetInclusion := by
  intro E body α Γ before after fuel vertices ctx ty seed
  let A := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have incl : Nonempty (Derivation body Δ (NumberedWindowInternalScratchInclusionThinProof.included before after)) := by
    apply NumberedWindowInternalScratchInclusionThinProof.introduce
    intro β j Θ k keep present
    have prev := renameInto ⟨Derivation.conjunctionLeft h⟩ j Θ keep
    have next := renameInto ⟨Derivation.conjunctionRight h⟩ j Θ keep
    rw [roundRename] at prev
    rw [roundRename,sucRelabel] at next
    obtain ⟨prev⟩ := prev
    obtain ⟨next⟩ := next
    obtain ⟨carry⟩ := exact_AdjacentRoundPersistence E body _ Θ (before.relabel j) (after.relabel j)
      (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) k
    obtain ⟨present⟩ := present
    exact ⟨Derivation.implicationElimination carry
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction prev next) present)⟩
  obtain ⟨incl⟩ := incl
  exact ⟨Derivation.implicationIntroduction incl⟩

theorem exact_NewMemberDecrease : ExactNewMemberDecrease := by
  intro strict E body α Γ before after fuel vertices ctx ty seed beforeCount afterCount k
  let stages := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let counts := graph2 NumberedWindowInternalThinUncoveredCount.count beforeCount vertices before ⊓
    graph2 NumberedWindowInternalThinUncoveredCount.count afterCount vertices after
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

#print axioms exact_BudgetInclusion
#print axioms exact_NewMemberDecrease
end LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundBudgetChecks

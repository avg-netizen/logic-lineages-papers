module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundBudgetChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.SourceComputabilityCompletion
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRoundBudgetChecks (exact_NewMemberDecrease)
open NumberedWindowInternalSparseRoundReachChecks (exact_RoundEdgeExtension)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseRoundAlternativeTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem oldMember (strict : PrimaryUncoveredCount.Targets.InternalStrictDecrease) (E : Program 4)
    (vertices ctx ty seed fuel before after bc ac k : OTerm α)
    (data : Derivation body Γ (budgetStep E vertices ctx ty seed fuel before after bc ac))
    (same : Derivation body Γ (drops ac bc).not) (afterHit : Derivation body Γ (memberGraph after k)) :
    Nonempty (Derivation body Γ (memberGraph before k)) := by
  let M := memberGraph before k
  apply formulaCases M
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · obtain ⟨law⟩ := exact_NewMemberDecrease strict E body α (M.not :: Γ) before after fuel vertices ctx ty seed bc ac k
    have h := addHyp data M.not
    have new := Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self : Derivation body (M.not :: Γ) M.not)
      (addHyp afterHit M.not)
    have fall := Derivation.implicationElimination law (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft h) (Derivation.conjunctionIntroduction (Derivation.conjunctionRight h) new))
    exact ⟨Derivation.explosion (Derivation.implicationElimination (addHyp same M.not) fall)⟩

theorem exact_RoundAlternative : ExactRoundAlternative := by
  intro strict E body α Γ vertices ctx ty seed fuel before after bc ac
  let A := budgetStep E vertices ctx ty seed fuel before after bc ac
  let D := drops ac bc
  let Δ := A :: Γ
  have data : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have alternative : Nonempty (Derivation body Δ (PrimaryMonotonicity.included after before ⊔ D)) := by
    apply formulaCases D
    · exact ⟨orRight (Derivation.hypothesis List.mem_cons_self)⟩
    · let Θ := D.not :: Δ
      have backward : Nonempty (Derivation body Θ (PrimaryMonotonicity.included after before)) := by
        apply ID1Completion.InternalClosedProgramsBindingProof.introduction body α 1 Θ
        let j : α → α ⊕ Fin 1 := Sum.inl
        let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
        let M := graph2 contains (numeral 1) (after.relabel j) k
        let Ξ := M :: Θ.map weaken
        have keep (p : Formula α) (hp : p ∈ Θ) : p.relabel j ∈ Ξ :=
          List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
        have d := renameInto ⟨addHyp data D.not⟩ j Ξ keep
        simp only [A,budgetStep,conjunctionRename,roundRename,sucRelabel,graph2Rename] at d
        have no : Derivation body Θ D.not := Derivation.hypothesis List.mem_cons_self
        have no' := renameInto ⟨no⟩ j Ξ keep
        change Nonempty (Derivation body Ξ ((ltF ac bc).relabel j).not) at no'
        rw [orderRename] at no'
        obtain ⟨h⟩ := d
        obtain ⟨n⟩ := no'
        obtain ⟨present⟩ := oldMember strict E (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
          (seed.relabel j) (fuel.relabel j) (before.relabel j) (after.relabel j)
          (bc.relabel j) (ac.relabel j) k h n (Derivation.hypothesis List.mem_cons_self : Derivation body Ξ M)
        exact ⟨Derivation.implicationIntroduction present⟩
      obtain ⟨inc⟩ := backward
      exact ⟨orLeft inc⟩
  obtain ⟨alt⟩ := alternative
  exact ⟨Derivation.implicationIntroduction alt⟩

theorem exact_ClosedWithoutDecrease : ExactClosedWithoutDecrease := by
  intro strict E body α Γ vertices ctx ty seed fuel before after bc ac w k
  let step := budgetStep E vertices ctx ty seed fuel before after bc ac
  let edge := (memberGraph before w ⊓ acceptEdge E ctx ty w k) ⊓ memberGraph vertices k
  let A := step ⊓ ((drops ac bc).not ⊓ edge)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have run := Derivation.conjunctionLeft h
  have rest := Derivation.conjunctionRight h
  obtain ⟨extend⟩ := exact_RoundEdgeExtension E body α Δ before after fuel vertices ctx ty seed w k
  have hit := Derivation.implicationElimination extend
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft run) (Derivation.conjunctionRight rest))
  obtain ⟨already⟩ := oldMember strict E vertices ctx ty seed fuel before after bc ac k run
    (Derivation.conjunctionLeft rest) hit
  exact ⟨Derivation.implicationIntroduction already⟩

#print axioms exact_RoundAlternative
#print axioms exact_ClosedWithoutDecrease
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundAlternativeChecks

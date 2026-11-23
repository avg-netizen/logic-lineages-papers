module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankedNeutralTypeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue valueUnique programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalNeutralRankGuard
open NumberedWindowInternalRankedNeutralTypeProof (RankedNeutralApplication)

private theorem acceptsGraph {α : Type} (p : Program 3) (x w y : OTerm α) :
    accepts p x w y = programGraph p (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem targetReport (g : Program 1) (x w y t : OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (atTarget g) t ![x,w,y]))) :
    Nonempty (Derivation B Γ (unary g t y)) := by
  unfold atTarget at held
  apply compositionRecover g (fun _ : Fin 1 => .projection (2 : Fin 3)) t ![x,w,y] ![y] held
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue 2 ![x,w,y]

/-- A genuine `targetHasRank` object call eliminates the zero branch and
exposes precisely the original freshly-bound positive graph output. -/
theorem targetRankCases (g : Program 1) (x w y : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (programGraph (targetHasRank g) (suc z) ![x,w,y])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ q ∈ Γ, q.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (unary g (suc m) (y.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  unfold targetHasRank at held
  apply optionGraphCases (atTarget g) (![x,w,y] : Fin 3 → OTerm α) goal
  · intro β j Δ keep absent
    rw [tripleInputsRename] at absent
    have h := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at h
    let ys : Fin 3 → OTerm β := ![x.relabel j,w.relabel j,y.relabel j]
    have bad := zeroBranchElim (atTarget g) (constantZero 3) (constantOne 3)
      (suc z) ys absent h
    obtain ⟨impossible⟩ := valueUnique (constantZero 3) (suc z) z ys bad (constantZeroValue ys)
    exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩
  · intro β j Δ m keep there
    rw [tripleInputsRename] at there
    exact next β j Δ m keep (targetReport g (x.relabel j) (w.relabel j) (y.relabel j) (suc m) there)

/-- The actual ranked p supplies a checked object-rank output and original
scalar carrier, in the same data choice, with no numerical reflection. -/
theorem exact_OpenRankGuardedApplication (i j g : Program 1) (r d p : Program 3) (c : Nat) :
    RankedNeutralApplication (data i j r d) g (rankApplication i g p) c := by
  intro α Γ k f u y goal src app next
  let S := data i j r d
  let B := sourceBody S c
  let xs : Fin 3 → OTerm α := ![f,u,y]
  have initial : Nonempty (Derivation B Γ (programGraph (atSource g) (suc k) xs)) :=
    callSlot g 0 (suc k) xs src
  rw [acceptsGraph,rankApplication] at app
  obtain ⟨both⟩ := conjunctionRecover p (conjunction (targetHasRank g) (atTarget i)) xs
    (successorBranchElim (atSource g) p (conjunction p (conjunction (targetHasRank g) (atTarget i)))
      (suc z) k xs initial app)
  obtain ⟨result⟩ := conjunctionRecover (targetHasRank g) (atTarget i) xs ⟨Derivation.conjunctionRight both⟩
  have guard : Nonempty (Derivation B Γ (programGraph (atTarget i) (suc z) xs)) :=
    ⟨Derivation.conjunctionRight result⟩
  apply targetRankCases g f u y goal ⟨Derivation.conjunctionLeft result⟩
  intro β rename Δ m keep rankY
  have guard' := renameInto guard rename Δ keep
  simp only [xs,programRename,tripleInputsRename,sucRelabel,zRelabel] at guard'
  have scalar := targetReport i (f.relabel rename) (u.relabel rename) (y.relabel rename) (suc z) guard'
  exact next β rename Δ m keep rankY
    ((exact_DomainRules i j r d false c B β Δ (y.relabel rename)).2 scalar)

#print axioms targetReport
#print axioms targetRankCases
#print axioms exact_OpenRankGuardedApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof

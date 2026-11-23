module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRefinedPositiveProjectionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalAtomicRefinement
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem physical (i : Program 1) (r : Program 3) :
    refined i r =
      branch (atSource freeSource) (branch (atSource bottomSource) r (constantZero 3))
        (conjunction r (conjunction bottomTarget (atTarget i))) := by
  unfold refined
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.2.2.2.2.1,
    exact_DispatchControlAST.1,exact_DispatchControlAST.2.2.2.2.2,
    exact_DispatchControlAST.2.2.2.2.2]

private theorem reportMove {β : Type} {Δ : List (Formula β)}
    (p : Program 3) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph p (suc z) xs)))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (programGraph p (suc z) (fun h => (xs h).relabel j))) := by
  simpa only [programRename,sucRelabel,zRelabel] using renameInto h j Δ keep

private theorem inner (r : Program 3) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (branch (atSource bottomSource) r (constantZero 3))
      (suc z) xs))) :
    Nonempty (Derivation B Γ (programGraph r (suc z) xs)) := by
  apply optionGraphCases (atSource bottomSource) xs (programGraph r (suc z) xs)
  · intro β j Δ keep clear
    simp only [programRename,sucRelabel,zRelabel]
    exact zeroBranchElim (atSource bottomSource) r (constantZero 3) (suc z)
      (fun q => (xs q).relabel j) clear (reportMove _ xs h j keep)
  · intro β j Δ k keep hit
    let ys := fun q => (xs q).relabel j
    have bad := successorBranchElim (atSource bottomSource) r (constantZero 3) (suc z) k ys hit
      (reportMove _ xs h j keep)
    obtain ⟨e⟩ := valueUnique (constantZero 3) (suc z) z ys bad (constantZeroValue ys)
    exact ⟨Derivation.explosion (sucNeZeroApply e)⟩

/-- Positive acceptance in the literal refinement implies an actual
positive report of the underlying exact checker on the same three
terms, in the same object body. No source-shape assumption or transport
of derivations between bodies is used. -/
theorem exact_OriginalRefinedPositiveProjection (i : Program 1) (r : Program 3)
    (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (refined i r) (suc z) xs))) :
    Nonempty (Derivation B Γ (programGraph r (suc z) xs)) := by
  let zeroArm := branch (atSource bottomSource) r (constantZero 3)
  let must := conjunction bottomTarget (atTarget i)
  have g : Nonempty (Derivation B Γ
      (programGraph (branch (atSource freeSource) zeroArm (conjunction r must)) (suc z) xs)) := by
    simpa only [physical,zeroArm,must] using h
  apply optionGraphCases (atSource freeSource) xs (programGraph r (suc z) xs)
  · intro β j Δ keep clear
    simp only [programRename,sucRelabel,zRelabel]
    apply inner
    exact zeroBranchElim (atSource freeSource) zeroArm (conjunction r must) (suc z)
      (fun q => (xs q).relabel j) clear (reportMove _ xs g j keep)
  · intro β j Δ k keep hit
    simp only [programRename,sucRelabel,zRelabel]
    let ys := fun q => (xs q).relabel j
    obtain ⟨both⟩ := conjunctionRecover r must ys
      (successorBranchElim (atSource freeSource) zeroArm (conjunction r must) (suc z) k ys hit
        (reportMove _ xs g j keep))
    exact ⟨Derivation.conjunctionLeft both⟩

#print axioms exact_OriginalRefinedPositiveProjection
end LogicLineages.PersistentMarking.NumberedWindowInternalRefinedPositiveProjectionProof

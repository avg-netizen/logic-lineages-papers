module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionOrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalSquareRootArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof InternalAcceptanceSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalContextInsertionBelowCoreProof (successorStrict)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A later distinct cutoff has an actual predecessor; the zero branch is
eliminated by internal arithmetic, not by inspecting a native natural. -/
theorem laterSuccessorCases (i j : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (ltF (suc i) (suc j))))
    (step : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (pred : OTerm beta),
      (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
      Nonempty (Derivation body Theta (eqn (j.relabel rho) (suc pred))) →
      Nonempty (Derivation body Theta (psi.relabel rho))) :
    Nonempty (Derivation body Delta psi) := by
  have hij := successorStrict i j h
  apply zeroSuccessorCases Delta j psi
  · obtain ⟨hij⟩ := withHyp hij (eqn j z)
    have he : Derivation body (eqn j z :: Delta) (eqn j z) := Derivation.hypothesis List.mem_cons_self
    have hz := orderRight i he hij
    obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha i
    exact ⟨Derivation.explosion (Derivation.implicationElimination (weakenClosed hn _) hz)⟩
  · exact step
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionOrderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionOrderProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions TypedExtraDownsets ConfinedStructuralInterpretation

theorem frameConfinement : ConfinedStructuralInterpretationTargets.FrameConfinement := by
  intro Symbol inst arity I q h
  exact ⟨h.1,h.2.1⟩

theorem sourceEquations : ConfinedStructuralInterpretationTargets.SourceEquations := by
  intro Symbol inst arity I
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro Γ τ v h
    rfl
  · intro Γ σ τ body h
    rfl
  · intro Γ f base h
    rfl
  · intro Γ f τ base ts extras h
    rfl
  · intro Γ ts σ q rest h
    rfl

theorem interpretationMonotone : ConfinedStructuralInterpretationTargets.InterpretationMonotone := by
  intro Symbol inst arity I Γ τ q
  exact (action q).evaluateMonotone

theorem interpretationNatural : ConfinedStructuralInterpretationTargets.InterpretationNatural := by
  intro Symbol inst arity I Γ τ q
  exact (action q).evaluateNatural

theorem scannerMonotone : ConfinedStructuralInterpretationTargets.ScannerMonotone := by
  intro Symbol inst arity I Γ τ q
  exact (action q).scanMonotone

theorem scannerNatural : ConfinedStructuralInterpretationTargets.ScannerNatural := by
  intro Symbol inst arity I Γ τ q
  exact (action q).scanNatural

theorem emptyScanner : ConfinedStructuralInterpretationTargets.EmptyScanner := by
  intro Symbol inst arity I Γ τ q M P ρ mask args
  exact (action q).scanEmpty M P ρ mask args

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedStructuralInterpretationProof

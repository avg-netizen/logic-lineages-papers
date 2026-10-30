module
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Simultaneous finite-height separation on the actual finite syntax closure.
No child induction, peak distinctness, or numerical budget premise survives. -/
def CollectedFiniteTailSeparation : Prop :=
  ∀ forms : List CollectedPositiveNF, (∀ A∈forms, CollectedPositiveValid A) →
    ∀ x : Nat, collectedFiniteZeroBound forms≤x →
      ∀ A∈collectedFiniteClosure forms, ∀ B∈collectedFiniteClosure forms,
        actualCollectedPositiveEval A x=actualCollectedPositiveEval B x ↔ A=B

end LogicLineages.OrdinalComparison.Targets

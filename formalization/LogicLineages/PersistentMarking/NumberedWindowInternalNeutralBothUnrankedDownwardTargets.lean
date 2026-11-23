module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedDownwardTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalDownwardTargets (matched)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z)

/-- The actual original earlier candidate and output edge are owed only
when the input edge has genuinely ranked-zero endpoints. -/
def BothUnrankedApplicationEdgeMatching (S : Data) (g : Program 1) (p : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (f f' u v : OTerm α),
    Nonempty (Derivation (sourceBody S c) Γ (unary g z f)) →
    Nonempty (Derivation (sourceBody S c) Γ (unary g z f')) →
    Nonempty (Derivation (sourceBody S c) Γ (edge S false c f f')) →
    Nonempty (Derivation (sourceBody S c) Γ (accepts p f' u v)) →
    Nonempty (Derivation (sourceBody S c) Γ (matched S p c f u v))

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedDownwardTargets

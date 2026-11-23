module

public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPullbackTargets (forwardImage)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z)

/-- The true even edge always yields the original scalar carrier on its
same real target, irrespective of the source rank. -/
def EdgeTargetCarriers (S : Data) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (f f' : OTerm α),
    Nonempty (Derivation (sourceBody S c) Γ (edge S false c f f')) →
    Nonempty (Derivation (sourceBody S c) Γ (carrier S false c f'))

/-- The unchanged forward image is owed only for an original edge
with genuine zero-rank reports at both endpoints. -/
def BothUnrankedForwardRule (S : Data) (g : Program 1) (p : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (f f' u x : OTerm α),
    Nonempty (Derivation (sourceBody S c) Γ (unary g z f)) →
    Nonempty (Derivation (sourceBody S c) Γ (unary g z f')) →
    Nonempty (Derivation (sourceBody S c) Γ (accepts p f u x)) →
    Nonempty (Derivation (sourceBody S c) Γ (edge S false c f f')) →
    Nonempty (Derivation (sourceBody S c) Γ (forwardImage S p c f' u x))

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackTargets

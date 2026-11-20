module
public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalPresentationTargets (data)

/-- The existential result is the application at the later function, with
the image edge pointing from the given earlier result to the new one. -/
def forwardImage (s : Data) (p : Program 3) (c : Nat) {α : Type} (g u x : OrdinaryArithmetic.Term α) :
    Formula α :=
  existsOne (accepts p (g.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) ⊓
    edge s false c (x.relabel Sum.inl) (.var (.inr 0)))

def ForwardRule (s : Data) (p : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (f g u x : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody s c) Γ (accepts p f u x)) →
    Nonempty (Derivation (sourceBody s c) Γ (edge s false c f g)) →
    Nonempty (Derivation (sourceBody s c) Γ (forwardImage s p c g u x))

def Pullback (s : Data) (p : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (f u x : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody s c) Γ (accepts p f u x)) →
    Nonempty (Derivation (sourceBody s c) Γ (membership false x)) →
    Nonempty (Derivation (sourceBody s c) Γ (membership false f))

def InternalPullback : Prop :=
  ∀ (i j : Program 1) (r d p : Program 3) (c : Nat),
    InputGuards i j r d p → ForwardRule (data i j r d) p c → Pullback (data i j r d) p c
end LogicLineages.PersistentMarking.NumberedWindowInternalPullbackTargets

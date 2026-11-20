module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramTargets
public import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchSelectionTargets
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentation (Data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (graph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- The original fixed S,K specialization is a separate checked bridge.
This statement has an explicit numerical source interface, not a new
axiom of ID1. p and a are used unchanged. -/
def SelectedTypedFromValid : Prop :=
  ∀ (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (p : Program 3) (a : Program 1),
      (∀ q u v, evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s q u v).toNat) →
      (∀ q, evaluate a (q ::ᵥ nil) = Encodable.encode (probe s q)) →
      ∃ h : Program 2,
        (∀ t q, evaluate h (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
        ∀ (d : Data) (c : Nat), TypedProbeTotal d p h a c

open NumberedWindowFunctionalGraphTargets NumberedWindowGuardedGraphTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)

def ConcreteTypedFromValid : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d p : Program 3) (h : Program 2) (a : Program 1),
      Evaluates (checks xs s) i j r d ∧
      Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
      (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
      UniqueResult p ∧ InputGuards i j r d p ∧
      (∀ n, evaluate a (n ::ᵥ nil) = Encodable.encode (probe s n)) ∧
      (∀ t q, evaluate h (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
      ∀ c, TypedProbeTotal (data i j r d) p h a c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchSelectionTargets

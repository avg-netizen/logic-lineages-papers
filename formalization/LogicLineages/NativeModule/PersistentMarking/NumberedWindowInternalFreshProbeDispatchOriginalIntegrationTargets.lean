module

public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowTypedProbe

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalIntegrationTargets
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentation (Data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (graph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Source-specific selection. Preserve the given original p and a as
literal Programs and choose one actual h for both calibration and
arbitrary-open object totality. No ValidWindow or object typing premise
about an old h0 is assumed. -/
def ExactOriginalSelectedProbeTypedTotal : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ (p : Program 3) (a : Program 1),
      (∀ q u v, evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph (fixed S K) q u v).toNat) →
      (∀ q, evaluate a (q ::ᵥ nil) = Encodable.encode (probe (fixed S K) q)) →
      ∃ h : Program 2,
        (∀ t q, evaluate h (t ::ᵥ q ::ᵥ nil) = (typed (fixed S K) t q).toNat) ∧
        ∀ (d : Data) (c : Nat), TypedProbeTotal d p h a c

open NumberedWindowFunctionalGraphTargets NumberedWindowGuardedGraphTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)

/-- Original source S,K with the same #596 i,j,r,d,p, exact checker
interpretation, rules, input guards and one chosen h,a. -/
def ExactOriginalConcreteProbeTypedTotal : Prop :=
  ∀ (xs : Entries) (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    let s := fixed S K
    ∃ (i j : Program 1) (r d p : Program 3) (h : Program 2) (a : Program 1),
      Evaluates (checks xs s) i j r d ∧
      Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
      (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
      UniqueResult p ∧ InputGuards i j r d p ∧
      (∀ n, evaluate a (n ::ᵥ nil) = Encodable.encode (probe s n)) ∧
      (∀ t q, evaluate h (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
      ∀ c, TypedProbeTotal (data i j r d) p h a c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalIntegrationTargets

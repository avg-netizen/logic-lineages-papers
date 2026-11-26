import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowAdmissionTargets
import LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFixedTypeWindowProof

open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowAdmissionTargets (typesIn)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowProbeCode (code)
open TypeSupport (subtypes)

/-- The two original encodings are literally the same arithmetic
recursion. This proof does not import the probe-totality bridge. -/
private theorem codeFormulaType (t : Ty) : code (formulaType t) = encodeTy t := by
  induction t with
  | ground => rfl
  | arrow a b ha hb =>
    simp [formulaType,code,encodeTy,ha,hb,NumberedWindowActualPairAlgorithmChecks.currentPair]

/-- Exactly the source codes are in the fixed admission window once the
original source window is closed. There is no extra ground assumption;
the empty window is allowed as well. -/
theorem exact_FixedFiniteCodesInTypeWindow (S : Spine.Signature) (K : List Ty)
    (closed : DecisionSourceUniverse.Closed K) :
    ∀ n ∈ (sourceWindow K).map code, n ∈ (fixed S K).window.1 := by
  intro n h
  obtain ⟨p,linked,rfl⟩ := List.mem_map.mp h
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp linked
  rw [codeFormulaType]
  change encodeTy t ∈ (K.filter (fun σ => typesIn K (subtypes σ))).map encodeTy
  apply List.mem_map.mpr
  refine ⟨t,List.mem_filter.mpr ⟨ht,?_⟩,rfl⟩
  exact List.all_eq_true.mpr (fun u hu => decide_eq_true (closed t ht u hu))

#print axioms exact_FixedFiniteCodesInTypeWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFixedTypeWindowProof

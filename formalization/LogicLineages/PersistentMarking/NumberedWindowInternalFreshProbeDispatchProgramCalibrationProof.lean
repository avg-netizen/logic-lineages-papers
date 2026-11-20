module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramCalibrationProof
open NumberedWindowInternalFreshProbeDispatchWindowTargets
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchProgramTargets
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
open NumberedWindowProbeCode (code)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (graph application)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

attribute [local instance] Classical.propDecidable

theorem typeLeafEvaluation (l : Leaves) (τ : ProbeTy) (q : Nat) :
    evaluate (typeLeaf l τ) (q ::ᵥ nil) = evaluate l.baseTyped (code τ ::ᵥ q ::ᵥ nil) := by
  rw [typeLeaf,compositeTwo,literalEvaluation] <;> rfl

private theorem afterPredEvaluation {n : Nat} (a : Program n) (xs : List.Vector Nat n) :
    evaluate (afterPredecessor a) xs = (evaluate a xs).pred := by
  rw [afterPredecessor,compositeOne,predEvaluation]

private theorem resultEvaluation (l : Leaves) (k : Program 1) (q u v : Nat) :
    evaluate (resultGuard l k) (q ::ᵥ u ::ᵥ v ::ᵥ nil) =
      if evaluate l.applicationGuard (q ::ᵥ u ::ᵥ v ::ᵥ nil) = 1 ∧ evaluate k (v ::ᵥ nil) = 1
      then 1 else 0 := by
  rw [resultGuard,bothEvaluation,compositeOne] <;> rfl

private theorem applicationEvaluation (l : Leaves) (k : Program 1) (q u : Nat) :
    evaluate (applicationPart l k) (q ::ᵥ u ::ᵥ nil) =
      let e := evaluate l.applicationCode (q ::ᵥ u ::ᵥ nil)
      if e = 0 then 0 else evaluate (resultGuard l k) (q ::ᵥ u ::ᵥ e.pred ::ᵥ nil) := by
  rw [applicationPart,branchEvaluation,zeroEvaluation,compositeThree,afterPredEvaluation] <;> rfl

private theorem arrowEvaluation (l : Leaves) (k : Program 1) (q : Nat) :
    evaluate (arrowPart l k) (q ::ᵥ nil) =
      let e := evaluate l.fresh (q ::ᵥ nil)
      if e = 0 then 0 else evaluate (applicationPart l k) (q ::ᵥ e.pred ::ᵥ nil) := by
  rw [arrowPart,branchEvaluation,zeroEvaluation,compositeTwo,afterPredEvaluation] <;> rfl

theorem typeTestEvaluation (τ : ProbeTy) (t q : Nat) :
    evaluate (typeTest τ) (t ::ᵥ q ::ᵥ nil) = if t = code τ then 1 else 0 := by
  rw [typeTest,compositeTwo,literalEvaluation]
  exact compareEvaluation t (code τ)

private theorem liftedEvaluation (l : Leaves) (τ : ProbeTy) (t q : Nat) :
    evaluate (liftBranch l τ) (t ::ᵥ q ::ᵥ nil) = evaluate (verify l τ) (q ::ᵥ nil) := by
  rw [liftBranch,compositeOne] <;> rfl

private theorem dispatchStep (l : Leaves) (τ : ProbeTy) (W : List ProbeTy) (t q : Nat) :
    evaluate (dispatch l (τ :: W)) (t ::ᵥ q ::ᵥ nil) =
      if t = code τ then evaluate (verify l τ) (q ::ᵥ nil)
      else evaluate (dispatch l W) (t ::ᵥ q ::ᵥ nil) := by
  rw [dispatch,branchEvaluation,typeTestEvaluation,liftedEvaluation]
  by_cases h : t = code τ <;> simp [h]

private theorem someCode (u : Nat) : Encodable.encode (some u : Option Nat) = u.succ := by
  simp

theorem verifyCalibration : ExactProbeVerifyCalibration := by
  intro s hn l hl τ
  induction τ with
  | ground =>
    intro q
    rw [verify,typeLeafEvaluation,hl.1]
  | arrow σ τ _ ih =>
    intro q
    rw [verify,bothEvaluation,typeLeafEvaluation,hl.1]
    cases ht : typed s (code (.arrow σ τ)) q with
    | false => simp
    | true =>
      obtain ⟨u,v,hu,hg,hv⟩ := hn σ τ q ht
      have happ : application s q u = some v := by
        simpa only [graph,beq_iff_eq] using hg
      have hFresh : evaluate l.fresh (q ::ᵥ nil) = u.succ := by
        rw [hl.2.1,hu,someCode]
      have hApp : evaluate l.applicationCode (q ::ᵥ u ::ᵥ nil) = v.succ := by
        rw [hl.2.2.1,happ,someCode]
      have hGuard : evaluate l.applicationGuard (q ::ᵥ u ::ᵥ v ::ᵥ nil) = 1 := by
        rw [hl.2.2.2,hg] <;> rfl
      have hChild : evaluate (verify l τ) (v ::ᵥ nil) = 1 := by
        rw [ih v,hv] <;> rfl
      have hArrow : evaluate (arrowPart l (verify l τ)) (q ::ᵥ nil) = 1 := by
        rw [arrowEvaluation,hFresh,if_neg (Nat.succ_ne_zero u),Nat.pred_succ,
          applicationEvaluation,hApp,if_neg (Nat.succ_ne_zero v),Nat.pred_succ,
          resultEvaluation,hGuard,hChild] <;> simp
      simp [hArrow]

/-- Pure finite lookup, retaining zero for an absent raw type. The theorem
below pays exact original support rather than assuming this default valid. -/
private theorem dispatchLookup (l : Leaves) (W : List ProbeTy) (t q : Nat) (result : Nat)
    (hv : ∀ τ, t = code τ → evaluate (verify l τ) (q ::ᵥ nil) = result) :
    evaluate (dispatch l W) (t ::ᵥ q ::ᵥ nil) =
      if (∃ τ ∈ W, t = code τ) then result else 0 := by
  induction W with
  | nil => simp [dispatch,zeroEvaluation]
  | cons τ tail ih =>
    rw [dispatchStep]
    by_cases he : t = code τ
    · have hm : ∃ ρ ∈ τ :: tail, t = code ρ := ⟨τ,List.mem_cons_self,he⟩
      rw [if_pos he,if_pos hm,hv τ he]
    · have rest : (∃ ρ ∈ τ :: tail, t = code ρ) ↔ ∃ ρ ∈ tail, t = code ρ := by
        constructor
        · rintro ⟨ρ,hρ,hc⟩
          rcases List.mem_cons.mp hρ with rfl | htail
          · exact False.elim (he hc)
          · exact ⟨ρ,htail,hc⟩
        · rintro ⟨ρ,hρ,hc⟩
          exact ⟨ρ,List.mem_cons_of_mem _ hρ,hc⟩
      rw [if_neg he,ih]
      by_cases htail : ∃ ρ ∈ tail, t = code ρ
      · rw [if_pos htail,if_pos (rest.mpr htail)]
      · have hcons : ¬ ∃ ρ ∈ τ :: tail, t = code ρ := fun h => htail (rest.mp h)
        rw [if_neg htail,if_neg hcons]

theorem dispatchCalibration : ExactProbeDispatchCalibration := by
  intro s W hw l hl t q
  have hv (τ : ProbeTy) (he : t = code τ) :
      evaluate (verify l τ) (q ::ᵥ nil) = (typed s t q).toNat := by
    rw [he]
    exact verifyCalibration s hw.2.2 l hl τ q
  rw [dispatchLookup l W t q ((typed s t q).toNat) hv]
  by_cases h : ∃ τ ∈ W, t = code τ
  · rw [if_pos h]
  · rw [if_neg h]
    cases ht : typed s t q with
    | false => rfl
    | true => exact False.elim (h (hw.1 t q ht))

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramCalibrationProof

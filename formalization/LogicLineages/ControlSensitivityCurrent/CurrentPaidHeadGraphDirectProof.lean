module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphTailProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open CurrentUnitElimination (HoldsRaw)

theorem exactDirectTemplate : Targets.ExactDirectTemplate := by
  intro p f hf β hε hlim c δ Γ hg ray hRay t y
  let ξ := shiftHead β δ
  let base := RayBase β c
  let n := actualOrdinalNorm ξ
  let stop := max n base
  let wr := ray.width
  let wmax := directWidth wr δ
  let nums := exactPoints f ξ base
  have hn : nums.length=stop-n := exactPointLength f ξ base
  have hgrowth := (FullAddition.completeAddition.2.2.2 f hf).2.1
  have hshift := (exactIteration f hf β hε hlim δ).2.2.2
  change (direct hg δ n base (smallValues f) nums ray).holds p f (endValues t y) ↔
    n≤t ∧ y=J f ξ t
  rw [directFiber p f hf hg]
  constructor
  · rintro ⟨w,ht,hy,hgraph⟩
    change (prefixBody (evalLayout f w) wmax (wmax+1) n nums ||
      tailBody (evalLayout f w) wr δ n base (smallValues f)
        (ray.matrix.eval p f (byIndex (fun i => w (rayPlacement wr i)))))=true at hgraph
    rw [Bool.or_eq_true] at hgraph
    rcases hgraph with hp|hs
    · obtain ⟨j,hj,h0,h1⟩ := (prefixNumerical f w wmax (wmax+1) n nums).mp hp
      change w wmax=t at ht
      change w (wmax+1)=y at hy
      rw [ht] at h0
      rw [hy,exactPointValue f ξ base j (by rw [hn] at hj; exact hj)] at h1
      exact ⟨by omega,by rw [h0]; exact h1⟩
    · have H := (tailNumerical f w wr δ n base _).mp hs
      have hT := H.1
      change stop ≤ w wmax at hT
      rw [ht] at hT
      have ht' : n≤t := (Nat.le_max_left n base).trans hT
      have hi := tailChain f w wr δ n base _ H
      rw [ht] at hi
      have hr := observedRay p f ray w H.2.2.1 H.2.2.2.2.1
      have hv := (hRay (rayInputs (w (wr+1))) (w wr+1)).mp hr
      change w wr+1=J f β (base+w (wr+1)) at hv
      have hu : base+w (wr+1)=(f^[δ]) t := H.2.2.2.1.symm.trans hi
      have hY := H.2.2.2.2.2.1
      change w (wmax+1)=w wr+(δ+1) at hY
      rw [hy] at hY
      rw [hu] at hv
      refine ⟨ht',?_⟩
      rw [(hshift t ht').2]
      omega
  · rintro ⟨ht,hy⟩
    by_cases hsmall : t<stop
    · let w : Nat→Nat := fun j => if j=wmax then t else y
      have h0 : w wmax=t := by simp [w]
      have h1 : w (wmax+1)=y := by simp [w]
      refine ⟨w,h0,h1,?_⟩
      change (prefixBody (evalLayout f w) wmax (wmax+1) n nums || _)=true
      rw [Bool.or_eq_true]
      left
      apply (prefixNumerical f w wmax (wmax+1) n nums).mpr
      have hj : t-n<nums.length := by rw [hn]; omega
      refine ⟨t-n,hj,by rw [h0]; omega,?_⟩
      rw [h1,exactPointValue f ξ base (t-n) (by rw [hn] at hj; exact hj)]
      have hx : n+(t-n)=t := by omega
      rw [hx]
      exact hy
    · have hT : stop≤t := by omega
      let q := (f^[δ]) t
      have hb : base≤q := (Nat.le_max_right n base).trans
        (hT.trans (iterateLower f (fun u => (hgrowth u).le) δ t))
      let v := J f β q
      have hr : HoldsRaw p f ray (rayInputs (q-base)) v := by
        apply (hRay (rayInputs (q-base)) v).mpr
        have he : base+(q-base)=q := by omega
        change v=J f β (base+(q-base))
        rw [he]
      obtain ⟨w,hwt,hwy,htail⟩ := realizeTail p f ray δ n base t v hT hb hr
      refine ⟨w,hwt,?_,?_⟩
      · rw [hwy,hy,(hshift t ht).2]
      · change (_ || tailBody (evalLayout f w) wr δ n base (smallValues f)
          (ray.matrix.eval p f (byIndex (fun i => w (rayPlacement wr i)))))=true
        exact Bool.or_eq_true_iff.mpr (Or.inr ((tailNumerical f w wr δ n base _).mpr htail))

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

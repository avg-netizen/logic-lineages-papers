module
public import LogicLineages.OrdinalComparison.CompensatedSyncTargets
public import LogicLineages.OrdinalComparison.KernelTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem compensatedStrictNatGap {f : Nat → Nat} (hf : StrictMono f) (x y : Nat) (h : x ≤ y) :
    f x + y ≤ f y + x := by
  induction y, h using Nat.le_induction with
  | base => omega
  | succ y h ih =>
    have hs := hf (Nat.lt_succ_self y)
    change f y < f (y+1) at hs
    change f x + (y+1) ≤ f (y+1) + x
    omega

theorem actualCompensatedBudgetPreservation : Targets.ActualCompensatedBudgetPreservation := by
  intro a b x y hxy htotal
  have hgap := compensatedStrictNatGap Phi_strictMono (a+x) (b+y) htotal
  have hx := self_lt_Phi (a+x)
  have hy := self_lt_Phi (b+y)
  have hm := Phi_strictMono.monotone htotal
  change Phi (a+x)-a ≤ Phi (b+y)-b ∧ a+(Phi (a+x)-a) ≤ b+(Phi (b+y)-b)
  omega

theorem actualCompensatedSynchronizedTraces : Targets.ActualCompensatedSynchronizedTraces := by
  intro a b A B hAB he hnorm htotal
  dsimp only
  let g := compensatedPrefixControl a
  let h := compensatedPrefixControl b
  let C := actualControlledCount g A
  let D := actualControlledCount h B
  let lo := actualControlledStateAfter g A
  let hi := actualControlledStateAfter h B
  have hA := hAB.trans_lt he
  have hlo := actualControlledTraceFirstFinite g A hA
  have hhi := actualControlledTraceFirstFinite h B he
  have htrace : ∀ i : Nat, i ≤ C → i ≤ D → lo i ≤ hi i ∧
      actualOrdinalNorm (lo i) ≤ actualOrdinalNorm (hi i) ∧
      a+actualOrdinalNorm (lo i) ≤ b+actualOrdinalNorm (hi i) := by
    intro i
    induction i with
    | zero => intro _ _; exact ⟨hAB, hnorm, htotal⟩
    | succ i ih =>
      intro hiC hiD
      have hCi : i < C := by omega
      have hDi : i < D := by omega
      have hsl := hlo.2 i hCi.le
      have hsh := hhi.2 i hDi.le
      have hcomp := ih hCi.le hDi.le
      have hnlo := hsl.2.2 hCi
      have hnhi := hsh.2.2 hDi
      have hbud := actualCompensatedBudgetPreservation a b
        (actualOrdinalNorm (lo i)) (actualOrdinalNorm (hi i)) hcomp.2.1 hcomp.2.2
      have hdl := actualNonfiniteDecomposition (lo i) hnlo hsl.1
      have hdh := actualNonfiniteDecomposition (hi i) hnhi hsh.1
      change actualControlledStateAfter g A (i+1) ≤ actualControlledStateAfter h B (i+1) ∧ _
      rw [actualControlledStateAfter_succ, actualControlledStateAfter_succ]
      refine ⟨actualMaximumJointMonotone _ _ hdl.2.1.bot_lt
        (actualLimitPartMonotone hcomp.1) hdh.1 _ _ hbud.1, ?_⟩
      change actualOrdinalNorm (actualControlledStateAfter g A (i+1)) ≤
        actualOrdinalNorm (actualControlledStateAfter h B (i+1)) ∧ _
      simpa only [lo, hi, actualControlledStateAfter_succ,
        actualControlledStepNorm g (lo i) hnlo hsl.1,
        actualControlledStepNorm h (hi i) hnhi hsh.1] using hbud
  have hCD : C ≤ D := by
    by_contra hn
    have hDC : D < C := by omega
    have hcomp := (htrace D hDC.le le_rfl).1
    exact not_lt_of_ge (((hlo.2 D hDC.le).2.2 hDC).trans hcomp) hhi.1
  refine ⟨hCD, fun i hi => htrace i hi (hi.trans hCD), ?_⟩
  have hmid := (htrace C le_rfl hCD).2.2
  have hiter := iterate_index_mono (fun n => (compensatedPrefixControlBounds b).2 n |>.2.le)
    (actualOrdinalNorm B) hCD
  have hnc := actualControlledNormIteration h B he C hCD
  have hnd := actualControlledNormIteration h B he D le_rfl
  have hexit : actualOrdinalNorm (hi C) ≤ actualOrdinalNorm (hi D) := by
    rw [hnc, hnd]
    exact hiter
  exact hmid.trans (Nat.add_le_add_left hexit b)

end LogicLineages.OrdinalComparison

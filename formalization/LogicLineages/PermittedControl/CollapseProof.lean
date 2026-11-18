module
public import LogicLineages.PermittedControl.CollapseTargets
public import LogicLineages.PermittedControl.ControlProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds
public import LogicLineages.OrdinalComparison.ActualLimitPredecessor

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

 theorem control_self_le (f : Nat → Nat) (hf : ∀ n, G n ≤ f n) (n : Nat) : n ≤ f n :=
  (self_lt_Phi n).le.trans (hf n)

 theorem selectedControlAdmissibility : Targets.SelectedControlAdmissibility := by
  have hmono : ∀ f : Nat → Nat, (∀ n, 2 ^ (2 ^ f n) ≤ f (n + 1)) → StrictMono f := by
    intro f hf
    apply strictMono_nat_of_lt_succ
    intro n
    exact (Nat.lt_two_pow_self (n := f n)).trans_le
      ((Nat.lt_two_pow_self (n := 2 ^ f n)).le.trans (hf n))
  exact ⟨⟨hmono factorialControl factorialControl_separation, factorialControl_ge⟩,
    fun b => ⟨hmono (nearControl b) (nearControl_separation b), nearControl_ge b⟩⟩

 theorem collapse_nonfinite (f : Nat → Nat) (hf : ∀ n, G n ≤ f n)
    (a : Ordinal.{0}) (ha : a < epsilonZero) (hw : Ordinal.omega0 ≤ a) :
    f (actualOrdinalNorm a) < collapseWith f a := by
  let b := f (actualOrdinalNorm a)
  have hb : (b : Ordinal) < a := (Ordinal.natCast_lt_omega0 b).trans_le hw
  have hn : actualOrdinalNorm (b : Ordinal) ≤ f (actualOrdinalNorm a) := by
    rw [(ParametricActualCollapse.Proof.natural_facts b).2]
  have h := (ParametricActualCollapse.Proof.equation f a ha).1 (b : Ordinal) hb hn
  rw [ParametricActualCollapse.Proof.finiteValues f (control_self_le f hf) b] at h
  exact h

 theorem collapse_norm (f : Nat → Nat) (hf : ∀ n, G n ≤ f n)
    (a : Ordinal.{0}) (ha : a < epsilonZero) : actualOrdinalNorm a ≤ collapseWith f a := by
  by_cases hw : a < Ordinal.omega0
  · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hw
    rw [(ParametricActualCollapse.Proof.natural_facts n).2,
      ParametricActualCollapse.Proof.finiteValues f (control_self_le f hf) n]
  · exact (control_self_le f hf _).trans (collapse_nonfinite f hf a ha (le_of_not_gt hw)).le

 theorem collapse_finite_tail (f : Nat → Nat) (hf : ∀ n, G n ≤ f n)
    (a : Ordinal.{0}) (k : Nat) (ha : a < epsilonZero) :
    collapseWith f a + k ≤ collapseWith f (a + (k : Ordinal)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := actualFiniteTailClosureNorm a ha (k + 1)
    have hk := actualFiniteTailClosureNorm a ha k
    have hlt : a + (k : Ordinal) < a + ((k + 1 : Nat) : Ordinal) := by
      exact add_lt_add_left (by exact_mod_cast Nat.lt_succ_self k) a
    have hn : actualOrdinalNorm (a + (k : Ordinal)) ≤
        f (actualOrdinalNorm (a + ((k + 1 : Nat) : Ordinal))) := by
      rw [hk.2, ht.2]
      exact (by omega : actualOrdinalNorm a + k ≤ actualOrdinalNorm a + (k + 1)).trans
        (control_self_le f hf _)
    have hc := (ParametricActualCollapse.Proof.equation f _ ht.1).1 _ hlt hn
    omega

 theorem collapseEstimates : Targets.CollapseEstimates := by
  intro f _ hf
  exact ⟨fun a b ha hb hn => (ParametricActualCollapse.Proof.equation f a ha).1 b hb hn,
    ParametricActualCollapse.Proof.finiteValues f (control_self_le f hf),
    collapse_norm f hf, collapse_finite_tail f hf, collapse_nonfinite f hf⟩

 private theorem finite_interval (a x : Ordinal) (n : Nat)
    (hax : a ≤ x) (hx : x < a + (n : Ordinal)) :
    ∃ j : Nat, j < n ∧ x = a + (j : Ordinal) := by
  have hd : x - a < (n : Ordinal) := by
    apply (add_lt_add_iff_left a).mp
    rwa [Ordinal.add_sub_cancel_of_le hax]
  obtain ⟨j, hj⟩ := Ordinal.eq_natCast_of_le_natCast hd.le
  refine ⟨j, ?_, ?_⟩
  · rw [hj] at hd
    exact_mod_cast hd
  · rw [← hj]
    exact (Ordinal.add_sub_cancel_of_le hax).symm

 theorem singlePredecessor : Targets.SinglePredecessor := by
  intro f hmono hf a ha hlim n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let b := f (actualOrdinalNorm a + n)
      let eta := actualMaximumPredecessor a b
      have hm := actualMaximumPredecessor_correct a hlim.bot_lt ha b
      have hs : actualOrdinalNorm eta = b := actualLimitMaximumPredecessorSaturation a ha hlim b
      have heps : eta < epsilonZero := hm.1.1.trans ha
      have ht := actualFiniteTailClosureNorm a ha n
      change collapseWith f (a + (n : Ordinal)) = collapseWith f eta + 1
      apply Nat.le_antisymm
      · apply (ParametricActualCollapse.Proof.equation f _ ht.1).2
        intro x hx hn
        have hnb : actualOrdinalNorm x ≤ b := by simpa only [ht.2] using hn
        by_cases hxa : x < a
        · have hxe : x ≤ eta := hm.2 ⟨hxa, hnb⟩
          rcases lt_or_eq_of_le hxe with hlt | heq
          · have hncontrol : actualOrdinalNorm x ≤ f (actualOrdinalNorm eta) := by
              rw [hs]
              exact hnb.trans (control_self_le f hf b)
            exact ((ParametricActualCollapse.Proof.equation f eta heps).1 x hlt hncontrol).trans
              (Nat.le_succ _)
          · rw [heq]
        · obtain ⟨j, hj, heq⟩ := finite_interval a x n (le_of_not_gt hxa) hx
          let bj := f (actualOrdinalNorm a + j)
          let etaj := actualMaximumPredecessor a bj
          have hjb : bj < b := hmono (Nat.add_lt_add_left hj _)
          have hje : etaj < eta := actualLimitMaximumPredecessorStrictGrowth a ha hlim hjb
          have hnj : actualOrdinalNorm etaj = bj := actualLimitMaximumPredecessorSaturation a ha hlim bj
          have hncontrol : actualOrdinalNorm etaj ≤ f (actualOrdinalNorm eta) := by
            rw [hnj, hs]
            exact hjb.le.trans (control_self_le f hf b)
          have hc := (ParametricActualCollapse.Proof.equation f eta heps).1 etaj hje hncontrol
          rw [heq, ih j hj]
          exact Nat.add_le_add_right hc 1
      · apply (ParametricActualCollapse.Proof.equation f _ ht.1).1 eta
          (hm.1.1.trans_le le_self_add)
        rw [ht.2, hs]

 theorem selected_admissibility (f : Nat → Nat)
    (hf : f = factorialControl ∨ ∃ b : Nat, f = nearControl b) :
    StrictMono f ∧ ∀ n, G n ≤ f n := by
  rcases hf with rfl | ⟨b, rfl⟩
  · exact selectedControlAdmissibility.1
  · exact selectedControlAdmissibility.2 b

 theorem selectedCollapseEstimates : Targets.SelectedCollapseEstimates := by
  intro f hf
  exact collapseEstimates f (selected_admissibility f hf).1 (selected_admissibility f hf).2

 theorem selectedSinglePredecessor : Targets.SelectedSinglePredecessor := by
  intro f hf
  exact singlePredecessor f (selected_admissibility f hf).1 (selected_admissibility f hf).2

end LogicLineages.PermittedControl

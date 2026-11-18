module
public import LogicLineages.PermittedControl.TailGrowthProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorNumericProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison OrdinalComparison.ParametricActualCollapse
open Source.FunctionalDetector.Proof (twice_le_pow four_linear_le_power)

noncomputable def appValue (ctrl : Nat → Nat) (h : Ordinal) (s q : Nat) : Nat :=
  collapseWith ctrl (ordinalNaturalProduct Ordinal.omega0 h + ((s+q : Nat) : Ordinal))

theorem finite_tail_gap (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (a : Ordinal) (ha : a<epsilonZero) (s t : Nat) (hst : s≤t) :
    collapseWith ctrl (a+(s : Ordinal))+(t-s) ≤ collapseWith ctrl (a+(t : Ordinal)) := by
  have h := collapse_finite_tail ctrl (selected_threshold_admissible ctrl K hc).2
    (a+(s : Ordinal)) (t-s) (actualFiniteTailClosureNorm a ha s).1
  have he : a+(s : Ordinal)+((t-s : Nat) : Ordinal)=a+(t : Ordinal) := by
    rw [add_assoc,← Nat.cast_add,Nat.add_sub_of_le hst]
  rwa [he] at h

theorem tail_two_fourfold (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (a : Ordinal) (ha : a<epsilonZero) (hl : Order.IsSuccLimit a) (n : Nat) :
    4*collapseWith ctrl (a+(n : Ordinal))<collapseWith ctrl (a+((n+2 : Nat) : Ordinal)) := by
  have h1 := fixedHeadTailGrowth ctrl K hc a ha hl n
  have h2 := fixedHeadTailGrowth ctrl K hc a ha hl (n+1)
  rw [show n+1+1=n+2 by omega] at h2
  have p1 := twice_le_pow (collapseWith ctrl (a+(n : Ordinal)))
  have p2 := twice_le_pow (collapseWith ctrl (a+((n+1 : Nat) : Ordinal)))
  omega

theorem tail_gap_fourfold (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (a : Ordinal) (ha : a<epsilonZero) (hl : Order.IsSuccLimit a)
    (s t q : Nat) (hst : s+2≤t) :
    4*collapseWith ctrl (a+((s+q : Nat) : Ordinal))<collapseWith ctrl (a+((t+q : Nat) : Ordinal)) := by
  have h1 := tail_two_fourfold ctrl K hc a ha hl (s+q)
  have h2 := finite_tail_gap ctrl K hc a ha (s+q+2) (t+q) (by omega)
  omega

theorem head_domination (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (a b : Ordinal) (s t q : Nat)
    (ha : a<epsilonZero) (hb : b<epsilonZero)
    (hal : Order.IsSuccLimit a) (hbl : Order.IsSuccLimit b) (hab : a<b)
    (hn : actualOrdinalNorm a≤2*s) (hs : s≤q) (hq : 5≤q) :
    4*collapseWith ctrl (a+((s+q : Nat) : Ordinal))<collapseWith ctrl (b+((t+q : Nat) : Ordinal)) := by
  have hα := actualFiniteTailClosureNorm a ha (s+q+2)
  have hβ := actualFiniteTailClosureNorm b hb (t+q)
  have horder : a+((s+q+2 : Nat) : Ordinal)<b+((t+q : Nat) : Ordinal) :=
    (hbl.add_natCast_lt hab (s+q+2)).trans_le le_self_add
  have hbudget : actualOrdinalNorm (a+((s+q+2 : Nat) : Ordinal))≤
      ctrl (actualOrdinalNorm (b+((t+q : Nat) : Ordinal))) := by
    rw [hα.2,hβ.2]
    calc
      actualOrdinalNorm a+(s+q+2) ≤ 4*q+2 := by omega
      _ ≤ 2^(q+1) := four_linear_le_power q hq
      _ ≤ 2^(actualOrdinalNorm b+(t+q)+100) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ Phi (actualOrdinalNorm b+(t+q)) := two_pow_shift_le_Phi _
      _ ≤ ctrl (actualOrdinalNorm b+(t+q)) := (selected_threshold_admissible ctrl K hc).2 _
  have hstrict := (ParametricActualCollapse.Proof.equation ctrl _ hβ.1).1 _ horder hbudget
  have ht := tail_two_fourfold ctrl K hc a ha hal (s+q)
  omega
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof

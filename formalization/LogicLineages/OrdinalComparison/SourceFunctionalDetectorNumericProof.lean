module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorTargets
public import LogicLineages.OrdinalComparison.ActualTailSeparation
public import LogicLineages.OrdinalComparison.WWFiniteTailMonotonicityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof

noncomputable def appValue (h : Ordinal) (s q : Nat) : Nat :=
  actualCollapse (ordinalNaturalProduct Ordinal.omega0 h + ((s+q : Nat) : Ordinal))

theorem twice_le_pow (n : Nat) : 2*n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Nat.pow_succ]
      omega

theorem tail_two_fourfold (a : Ordinal) (ha : a<epsilonZero) (hl : Order.IsSuccLimit a) (n : Nat) :
    4*actualCollapse (a+(n : Ordinal))<actualCollapse (a+((n+2 : Nat) : Ordinal)) := by
  have h1 := (actualTailSeparation a ha hl).1 n
  have h2 := (actualTailSeparation a ha hl).1 (n+1)
  rw [show n+1+1=n+2 by omega] at h2
  have p1 := twice_le_pow (actualCollapse (a+(n : Ordinal)))
  have p2 := twice_le_pow (actualCollapse (a+((n+1 : Nat) : Ordinal)))
  omega

theorem tail_gap_fourfold (a : Ordinal) (ha : a<epsilonZero) (hl : Order.IsSuccLimit a)
    (s t q : Nat) (hst : s+2≤t) :
    4*actualCollapse (a+((s+q : Nat) : Ordinal))<actualCollapse (a+((t+q : Nat) : Ordinal)) := by
  exact (tail_two_fourfold a ha hl (s+q)).trans_le
    (actualCollapseFiniteTailMonotone a ha (s+q+2) (t+q) (by omega))

theorem four_linear_le_power (q : Nat) (hq : 5≤q) : 4*q+2≤2^(q+1) := by
  induction q, hq using Nat.le_induction with
  | base => decide
  | succ q hq ih =>
    rw [Nat.pow_succ]
    omega

/-- Controlled strictness is used only after its full norm budget is proved.
The limit-head/order/norm hypotheses are explicit obligations for source consumers. -/
theorem head_domination (a b : Ordinal) (s t q : Nat)
    (ha : a<epsilonZero) (hb : b<epsilonZero)
    (hal : Order.IsSuccLimit a) (hbl : Order.IsSuccLimit b) (hab : a<b)
    (hn : actualOrdinalNorm a≤2*s) (hs : s≤q) (hq : 5≤q) :
    4*actualCollapse (a+((s+q : Nat) : Ordinal))<actualCollapse (b+((t+q : Nat) : Ordinal)) := by
  have hα := actualFiniteTailClosureNorm a ha (s+q+2)
  have hβ := actualFiniteTailClosureNorm b hb (t+q)
  have horder : a+((s+q+2 : Nat) : Ordinal)<b+((t+q : Nat) : Ordinal) :=
    (hbl.add_natCast_lt hab (s+q+2)).trans_le le_self_add
  have hbudget : actualOrdinalNorm (a+((s+q+2 : Nat) : Ordinal))≤
      Phi (actualOrdinalNorm (b+((t+q : Nat) : Ordinal))) := by
    rw [hα.2,hβ.2]
    calc
      actualOrdinalNorm a+(s+q+2) ≤ 4*q+2 := by omega
      _ ≤ 2^(q+1) := four_linear_le_power q hq
      _ ≤ 2^(actualOrdinalNorm b+(t+q)+100) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ Phi (actualOrdinalNorm b+(t+q)) := two_pow_shift_le_Phi _
  have hc := actualCollapse_controlledStrictness _ hβ.1 _ horder hbudget
  have ht := tail_two_fourfold a ha hal (s+q)
  omega
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof

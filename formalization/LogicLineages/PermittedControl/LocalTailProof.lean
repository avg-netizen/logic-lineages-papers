module
public import LogicLineages.PermittedControl.LocalPhaseTargets
public import LogicLineages.PermittedControl.GapInputFoundationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem phase_power_below (a : Ordinal.{0}) (ha : a < epsilonZero) : Ordinal.omega0^a < epsilonZero :=
  (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha

 theorem successorLocalTail : Targets.SuccessorLocalTail := by
  intro a X ha hX
  have hs : a+1 < epsilonZero := by simpa using (actualFiniteTailClosureNorm a ha 1).1
  have hpos : 0 < a+1 := lt_of_le_of_lt zero_le (show a < a+1 from Order.lt_add_one_iff.mpr le_rfl)
  have hm : actualMaximumPredecessor (a+1) (X-1) = a := by
    apply Eq.symm
    apply actualMaximumPredecessor_unique (a+1) hpos hs (X-1) a
    refine ⟨⟨Order.lt_add_one_iff.mpr le_rfl, by omega⟩, ?_⟩
    intro y hy
    exact Order.lt_add_one_iff.mp hy.1
  have hr := actualLowerPowerGreedyRecurrence (a+1) hpos hs X (by omega)
  dsimp only at hr
  rw [hm] at hr
  exact hr

 theorem power_maximum_leading (a : Ordinal.{0}) (ha : a < epsilonZero) (hpos : 0 < a)
    (X : Nat) (hX : 0 < X) :
    0 < actualMaximumPredecessor (Ordinal.omega0^a) X ∧
    Ordinal.log Ordinal.omega0 (actualMaximumPredecessor (Ordinal.omega0^a) X) =
      actualMaximumPredecessor a (X-1) := by
  let q := actualMaximumPredecessor a (X-1)
  let v := 1+actualOrdinalNorm q
  have hq : q < epsilonZero := (actualMaximumPredecessor_correct a hpos ha (X-1)).1.1.trans ha
  have hp := phase_power_below q hq
  have ht := (actualMaximumPredecessor_correct (Ordinal.omega0^q)
    (Ordinal.opow_pos q Ordinal.omega0_pos) hp (X%v)).1.1
  have hcoef : 0 < X/v := (optimizedMaximumCallsDecrease.2.2.2 a hpos ha X hX).2.1
  have hc : ((X/v : Nat) : Ordinal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcoef
  have hcpos : 0 < ((X/v : Nat) : Ordinal) := by exact_mod_cast hcoef
  have hr := actualLowerPowerGreedyRecurrence a hpos ha X hX
  change actualMaximumPredecessor (Ordinal.omega0^a) X =
    Ordinal.omega0^q * ((X/v : Nat) : Ordinal) + actualMaximumPredecessor (Ordinal.omega0^q) (X%v) at hr
  rw [hr]
  refine ⟨(mul_pos (Ordinal.opow_pos q Ordinal.omega0_pos) hcpos).trans_le le_self_add, ?_⟩
  rw [Ordinal.log_opow_mul_add Ordinal.one_lt_omega0 hc ht,
    Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 _), add_zero]

 theorem limitLocalTail : Targets.LimitLocalTail := by
  intro a ha hl
  refine ⟨fun X hX => power_maximum_leading a ha hl.bot_lt X hX, ?_⟩
  intro X Y hX hXY
  rw [(power_maximum_leading a ha hl.bot_lt X hX).2,
    (power_maximum_leading a ha hl.bot_lt Y (by omega)).2]
  exact actualLimitMaximumPredecessorStrictGrowth a ha hl (by omega)

 theorem quadraticLocalCoincidence : Targets.QuadraticLocalCoincidence := by
  intro X Y hX hY hne
  have hform : ∀ b : Nat, 2 ≤ b →
      actualLimitPart (actualMaximumPredecessor (Ordinal.omega0^(2 : Ordinal)) b) =
        Ordinal.omega0*((b/2 : Nat) : Ordinal) := by
    intro b hb
    rw [actualOmegaSquaredMaximum b hb]
    have hq : 0 < ((b/2 : Nat) : Ordinal) := by exact_mod_cast (show 0 < b/2 by omega)
    exact limitPart_tail _ (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hq) _
  rw [hform X hX, hform Y hY]
  have hequiv : Ordinal.omega0*((X/2 : Nat) : Ordinal) = Ordinal.omega0*((Y/2 : Nat) : Ordinal) ↔ X/2=Y/2 := by
    constructor
    · intro h
      have hn := congrArg actualOrdinalNorm h
      have hx : actualOrdinalNorm (Ordinal.omega0*((X/2 : Nat) : Ordinal)) = 2*(X/2) := by
        simpa using actualFiniteHeadNorm (X/2) 0
      have hy : actualOrdinalNorm (Ordinal.omega0*((Y/2 : Nat) : Ordinal)) = 2*(Y/2) := by
        simpa using actualFiniteHeadNorm (Y/2) 0
      rw [hx,hy] at hn
      omega
    · intro h
      rw [h]
  rw [hequiv]
  omega

end LogicLineages.PermittedControl

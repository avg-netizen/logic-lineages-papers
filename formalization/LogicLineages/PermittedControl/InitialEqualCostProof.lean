module
public import LogicLineages.PermittedControl.EqualInitialStateProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- The equal-leading-cost branch of the frozen initial phase, with all
source-radius affordability conditions discharged. -/
 theorem initial_equal_cost_return (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hc : relativeProfile mu (Ordinal.log Ordinal.omega0 delta)=relativeProfile nu (Ordinal.log Ordinal.omega0 delta)) :
    ∃ i : Nat, FirstEntry f A (mu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
      FirstEntry f A' (nu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
      actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t ∧
      actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t := by
  let E := Ordinal.log Ordinal.omega0 delta
  let P := Ordinal.omega0^E
  have hE := (initial_leading_norm delta hd hdl.bot_lt.ne').1
  have hP : P < epsilonZero := phase_power_below E hE
  have hEpos : 0 < E := Ordinal.log_pos Ordinal.one_lt_omega0 hdl.bot_lt.ne' (Ordinal.omega0_le_of_isSuccLimit hdl)
  have hPl : Order.IsSuccLimit P := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hEpos.ne'
  have hlog : Ordinal.log Ordinal.omega0 P=E := Ordinal.log_opow Ordinal.one_lt_omega0 E
  have hPd : P ≤ delta := Ordinal.opow_log_le_self _ hdl.bot_lt.ne'
  have hband : delta < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) := by
    rw [hlog]
    exact Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
  have hR := initial_radius_bounds mu nu delta
  have hRt : initialPeelingRadius mu nu delta ≤ t := (by omega : initialPeelingRadius mu nu delta ≤ initialPeelingRadius mu nu delta+3).trans (sensitive_tail_large _ B t ht)
  have hbudget : actualOrdinalNorm (mu+P) ≤ t := by
    have hpN := (initial_leading_norm delta hd hdl.bot_lt.ne').2
    have hrel := relativeNorm mu P hmu hP
    have hbound : actualOrdinalNorm (mu+P) ≤ initialPeelingRadius mu nu delta := by
      dsimp [initialPeelingRadius]
      change actualOrdinalNorm P ≤ actualOrdinalNorm delta at hpN
      omega
    exact hbound.trans hRt
  exact equal_initial_state_return f B hf mu nu P delta A A' t hmu hnu hP hd hA hA' hPl hdl hmud hnud hPd hband
    (by simpa only [hlog] using hc) hpart hpart' hN hN' hbudget
    (max_le (hR.2.1.trans hRt) (hR.2.2.1.trans hRt))

end LogicLineages.PermittedControl

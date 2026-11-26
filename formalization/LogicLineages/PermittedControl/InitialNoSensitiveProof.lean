module
public import LogicLineages.PermittedControl.OriginalUnitsProof
public import LogicLineages.PermittedControl.InitialEqualCostProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actual_limit_norm_le (A L : Ordinal.{0}) (hA : A < epsilonZero)
    (hL : Order.IsSuccLimit L) (hp : actualLimitPart A=L) :
    actualOrdinalNorm L ≤ actualOrdinalNorm A := by
  have hn : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit hL).trans
    (by rw [← hp]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have h := (actualNonfiniteDecomposition A hn hA).2.2.2
  rw [hp] at h
  omega

 theorem initial_no_sensitive_return (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero) (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hs : ∀ e ∈ initialPeelingUnits delta, e < 2) :
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
  obtain ⟨n,hn⟩ := initial_no_sensitive_shape delta hd hdl hs
  change delta=P+Ordinal.omega0*(n : Ordinal) at hn
  have htarget (mu : Ordinal.{0}) (hmu : mu < epsilonZero) :
      actualOrdinalNorm (mu+P) ≤ actualOrdinalNorm delta+actualOrdinalNorm mu := by
    have hpN := (initial_leading_norm delta hd hdl.bot_lt.ne').2
    change actualOrdinalNorm P ≤ actualOrdinalNorm delta at hpN
    have hrel := relativeNorm mu P hmu hP
    omega
  have htm := htarget mu hmu
  have htn : actualOrdinalNorm (nu+P) ≤ actualOrdinalNorm delta+actualOrdinalNorm nu := by
    have hpN := (initial_leading_norm delta hd hdl.bot_lt.ne').2
    change actualOrdinalNorm P ≤ actualOrdinalNorm delta at hpN
    have hrel := relativeNorm nu P hnu hP
    omega
  have hRt := sensitive_tail_large _ B t ht
  have hhead := actual_limit_norm_le A (mu+delta) hA (Ordinal.isSuccLimit_add mu hdl) hpart
  have hhead' := actual_limit_norm_le A' (nu+delta) hA' (Ordinal.isSuccLimit_add nu hdl) hpart'
  rw [hN] at hhead
  rw [hN'] at hhead'
  have hg : max 2 (max (actualOrdinalNorm (mu+(P+Ordinal.omega0*(n : Ordinal))))
      (max (actualOrdinalNorm (nu+(P+Ordinal.omega0*(n : Ordinal))))
        (max (actualOrdinalNorm (mu+P)+3) (actualOrdinalNorm (nu+P)+3)))) ≤ t := by
    rw [← hn]
    dsimp [initialPeelingRadius] at hRt
    omega
  have h := actualLinearReturn f B hf mu nu P A A' n t hmu hnu hP hA hA' hPl
    (by rwa [← hn]) (by rwa [← hn]) hN hN' hg
  exact ⟨n,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

end LogicLineages.PermittedControl

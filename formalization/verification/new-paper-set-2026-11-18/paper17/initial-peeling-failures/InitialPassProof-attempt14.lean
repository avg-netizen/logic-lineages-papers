module
public import LogicLineages.PermittedControl.InitialExceptionalPassProof
public import LogicLineages.PermittedControl.OriginalUnitOrderProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem initial_pass_return (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hpass : initialPeelingPass mu nu delta) :
    ∃ i : Nat, FirstEntry f A (mu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
      FirstEntry f A' (nu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
      actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t ∧
      actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t := by
  rcases hpass with hc | hs | ⟨hadj,hex | hex⟩
  · exact initial_equal_cost_return f B hf mu nu delta A A' t hmu hnu hd hA hA' hmud hnud hdl ht hpart hpart' hN hN' hc
  · exact initial_no_sensitive_return f B hf mu nu delta A A' t hmu hnu hd hA hA' hdl ht hpart hpart' hN hN' hs
  · obtain ⟨hE,n,hshape,hodd⟩ := hex
    exact initial_quadratic_exception_pass f B hf mu nu delta A A' t n hmu hnu hd hA hA' hmud hnud hdl ht
      hpart hpart' hN hN' ((by exact_mod_cast (show (2 : Nat) ≤ 3 by omega) : (2 : Ordinal) ≤ 3).trans hE) hshape hadj hodd
  · obtain ⟨n,hshape,hodd⟩ := hex
    have htail : Ordinal.omega0*(n : Ordinal) < Ordinal.omega0^(2 : Ordinal) :=
      by
        have h := Ordinal.opow_mul_lt_opow (u := (1 : Ordinal)) (x := (2 : Ordinal)) (Ordinal.natCast_lt_omega0 n) (by norm_num)
        simpa using h
    have hlog : Ordinal.log Ordinal.omega0 delta=2 := by
      rw [hshape,Ordinal.log_opow_mul_add Ordinal.one_lt_omega0 (by norm_num : (2 : Ordinal) ≠ 0) htail,
        Ordinal.log_eq_zero (Ordinal.natCast_lt_omega0 2),add_zero]
    have hshape' : delta=Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal) := by
      rw [hlog,hshape]
      congr 1
      exact mul_two _
    have hodd' : (min (relativeProfile mu (Ordinal.log Ordinal.omega0 delta)) (relativeProfile nu (Ordinal.log Ordinal.omega0 delta))+
        actualOrdinalNorm (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)))%2=1 := by simpa only [hlog] using hodd
    exact initial_quadratic_exception_pass f B hf mu nu delta A A' t n hmu hnu hd hA hA' hmud hnud hdl ht
      hpart hpart' hN hN' (by rw [hlog]) hshape' hadj hodd'

end LogicLineages.PermittedControl

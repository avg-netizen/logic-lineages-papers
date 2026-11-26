module
public import LogicLineages.PermittedControl.InitialNormProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem equal_initial_state_return (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P delta A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hP : P < epsilonZero)
    (hd : delta < epsilonZero) (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hPl : Order.IsSuccLimit P) (hdl : Order.IsSuccLimit delta)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hPd : P ≤ delta) (hband : delta < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1))
    (hcost : relativeProfile mu (Ordinal.log Ordinal.omega0 P)=relativeProfile nu (Ordinal.log Ordinal.omega0 P))
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hbudget : actualOrdinalNorm (mu+P) ≤ t)
    (hprefix : max (actualOrdinalNorm mu) (actualOrdinalNorm nu) ≤ t) :
    ∃ i : Nat, FirstEntry f A (mu+P) i ∧ FirstEntry f A' (nu+P) i ∧
      actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t ∧
      actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t := by
  have hL := epsilonZero_add_principal hmu hd
  have hL' := epsilonZero_add_principal hnu hd
  have ha := (interval_iff_limitPart A _ (Or.inr (Ordinal.isSuccLimit_add mu hdl))).mpr hpart
  have ha' := (interval_iff_limitPart A' _ (Or.inr (Ordinal.isSuccLimit_add nu hdl))).mpr hpart'
  obtain ⟨n,hn⟩ := interval_tail A _ ha.1 ha.2
  obtain ⟨m,hm⟩ := interval_tail A' _ ha'.1 ha'.2
  have hheadN : actualOrdinalNorm (mu+delta)=actualOrdinalNorm (nu+delta) := by
    rw [(relativeNorm mu delta hmu hd).1,(relativeNorm nu delta hnu hd).1,
      retained_band_cost mu P delta hPl.bot_lt hPd hband,
      retained_band_cost nu P delta hPl.bot_lt hPd hband,hcost]
  have hnt := (actualFiniteTailClosureNorm (mu+delta) hL n).2
  have hmt := (actualFiniteTailClosureNorm (nu+delta) hL' m).2
  rw [← hn,hN] at hnt
  rw [← hm,hN',← hheadN] at hmt
  have hnm : n=m := by omega
  subst m
  have hy := (actualFiniteTailClosureNorm delta hd n).1
  have hPy : P ≤ delta+(n : Ordinal) := hPd.trans le_self_add
  have hlogpos : 0 < Ordinal.log Ordinal.omega0 P+1 := by exact Order.lt_add_one_iff.mpr bot_le
  have hnsmall : (n : Ordinal) < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    (Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.left_le_opow Ordinal.omega0 hlogpos)
  have hyband := Ordinal.isPrincipal_add_omega0_opow _ hband hnsmall
  have hNy : actualOrdinalNorm (mu+(delta+(n : Ordinal)))=t := by simpa only [← add_assoc,← hn] using hN
  obtain ⟨i,hi,hi'⟩ := equal_retained_return f B hf mu nu P hmu hnu hP hPl hmud hnud hcost
    _ hy hPy hyband (by rw [hNy]; exact hbudget) (by rw [hNy]; exact hprefix)
  have heA : A=mu+(delta+(n : Ordinal)) := by simpa only [add_assoc] using hn
  have heA' : A'=nu+(delta+(n : Ordinal)) := by simpa only [add_assoc] using hm
  rw [← heA] at hi
  rw [← heA'] at hi'
  refine ⟨i,hi,hi',?_,?_⟩
  · rw [← hN]
    exact trajectory_norm_nonfinite f A hA i ((Ordinal.omega0_le_of_isSuccLimit (Ordinal.isSuccLimit_add mu hPl)).trans hi.1)
  · rw [← hN']
    exact trajectory_norm_nonfinite f A' hA' i ((Ordinal.omega0_le_of_isSuccLimit (Ordinal.isSuccLimit_add nu hPl)).trans hi'.1)

end LogicLineages.PermittedControl

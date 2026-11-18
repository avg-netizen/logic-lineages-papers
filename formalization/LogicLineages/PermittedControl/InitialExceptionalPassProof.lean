module
public import LogicLineages.PermittedControl.QuadraticOriginalReturnProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem initial_quadratic_exception_pass (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu delta A A' : Ordinal.{0}) (t n : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hd : delta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hdl : Order.IsSuccLimit delta)
    (ht : thickBlockTail (initialPeelingRadius mu nu delta) B ≤ t)
    (hpart : actualLimitPart A=mu+delta) (hpart' : actualLimitPart A'=nu+delta)
    (hN : actualOrdinalNorm A=t) (hN' : actualOrdinalNorm A'=t)
    (hE2 : (2 : Ordinal) ≤ Ordinal.log Ordinal.omega0 delta)
    (hshape : delta=Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal))
    (hadj : relativeProfile mu (Ordinal.log Ordinal.omega0 delta)=relativeProfile nu (Ordinal.log Ordinal.omega0 delta)+1 ∨
      relativeProfile nu (Ordinal.log Ordinal.omega0 delta)=relativeProfile mu (Ordinal.log Ordinal.omega0 delta)+1)
    (hodd : (min (relativeProfile mu (Ordinal.log Ordinal.omega0 delta)) (relativeProfile nu (Ordinal.log Ordinal.omega0 delta))+
      actualOrdinalNorm (Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)))%2=1) :
    ∃ i : Nat, FirstEntry f A (mu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
      FirstEntry f A' (nu+Ordinal.omega0^(Ordinal.log Ordinal.omega0 delta)) i ∧
      actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] t ∧
      actualOrdinalNorm ((descentWith f)^[i] A')=f^[i] t := by
  let E := Ordinal.log Ordinal.omega0 delta
  let P := Ordinal.omega0^E
  let R := initialPeelingRadius mu nu delta
  have hlead := initial_leading_norm delta hd hdl.bot_lt.ne'
  have hP : P < epsilonZero := phase_power_below E hlead.1
  have hPpos : 0 < P := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hdiv : Ordinal.omega0^(2 : Ordinal) ∣ P := Ordinal.opow_dvd_opow Ordinal.omega0 hE2
  have hlog : Ordinal.log Ordinal.omega0 P=E := Ordinal.log_opow Ordinal.one_lt_omega0 E
  have hR := initial_radius_bounds mu nu delta
  have hPR : actualOrdinalNorm P ≤ R := hlead.2.trans hR.2.2.2
  have hp : actualLimitPart A=mu+((P+Ordinal.omega0^(2 : Ordinal))+Ordinal.omega0*(n : Ordinal)) := by rwa [← hshape]
  have hp' : actualLimitPart A'=nu+((P+Ordinal.omega0^(2 : Ordinal))+Ordinal.omega0*(n : Ordinal)) := by rwa [← hshape]
  rcases hadj with hadj | hadj
  · have hex : relativeProfile mu (Ordinal.log Ordinal.omega0 P)=relativeProfile nu (Ordinal.log Ordinal.omega0 P)+1 ∧
        (relativeProfile nu (Ordinal.log Ordinal.omega0 P)+actualOrdinalNorm P)%2=1 := by
      rw [hlog]
      refine ⟨hadj,?_⟩
      have hc : relativeProfile nu E ≤ relativeProfile mu E := by dsimp only [E]; omega
      simpa only [E,P,min_eq_right hc] using hodd
    obtain ⟨i,hi,hi',hni,hni'⟩ := quadratic_original_return f B hf nu mu P A' A n R t hnu hmu hP hA' hA hnud hmud
      hPpos hdiv hR.1 hR.2.2.1 hR.2.1 hPR ht hp' hp hN' hN hex
    exact ⟨i,hi',hi,hni',hni⟩
  · have hex : relativeProfile nu (Ordinal.log Ordinal.omega0 P)=relativeProfile mu (Ordinal.log Ordinal.omega0 P)+1 ∧
        (relativeProfile mu (Ordinal.log Ordinal.omega0 P)+actualOrdinalNorm P)%2=1 := by
      rw [hlog]
      refine ⟨hadj,?_⟩
      have hc : relativeProfile mu E ≤ relativeProfile nu E := by dsimp only [E]; omega
      simpa only [E,P,min_eq_left hc] using hodd
    exact quadratic_original_return f B hf mu nu P A A' n R t hmu hnu hP hA hA' hmud hnud
      hPpos hdiv hR.1 hR.2.1 hR.2.2.1 hPR ht hp hp' hN hN' hex

end LogicLineages.PermittedControl

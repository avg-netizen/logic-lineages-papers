import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassSpecProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassEqualityProof
open NumberedWindowPrimary NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassTargets
open NumberedWindowArithmeticLeastClassSpecProof

theorem leastEq : LeastCodeReflectsPrimary := by
  intro S K Γ τ Q R hk hQ hR
  obtain ⟨cq,U,hcq,_,hU,_,hQU,hLeastQ,_⟩ := specification S K Γ τ Q hk hQ
  obtain ⟨cr,V,hcr,_,hV,_,hRV,hLeastR,_⟩ := specification S K Γ τ R hk hR
  constructor
  · intro e
    have hc : cq = cr := Option.some.inj (hcq.symm.trans (e.trans hcr))
    have hUV : U = V := literalInj (hU.trans (hc.trans hV.symm))
    rw [hUV] at hQU
    exact .trans hQU (.symm hRV)
  · intro hp
    have hqr := hLeastQ V (.trans hp hRV)
    have hrq := hLeastR U (.trans (.symm hp) hQU)
    rw [hV] at hqr
    rw [hU] at hrq
    exact hcq.trans ((congrArg some (Nat.le_antisymm hqr hrq)).trans hcr.symm)

theorem representativeEq : RepresentativeReflectsPrimary := by
  intro S K Γ τ Q R hk hQ hR
  constructor
  · intro e
    obtain ⟨_,U,_,hq,_,_,hQU,_,_⟩ := specification S K Γ τ Q hk hQ
    obtain ⟨_,V,_,hr,_,_,hRV,_,_⟩ := specification S K Γ τ R hk hR
    have hUV : U = V := Option.some.inj (hq.symm.trans (e.trans hr))
    rw [hUV] at hQU
    exact .trans hQU (.symm hRV)
  · intro hp
    exact congrArg (fun o : Option Nat => o.bind decodeTerm)
      ((leastEq S K Γ τ Q R hk hQ hR).mpr hp)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassEqualityProof

import LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassChecks

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowPathWitnessTargets

theorem existsCode (S : Signature) (K Γ : List Ty) (τ : Ty)
    (hk : DecisionSourceUniverse.Closed K) (x : Class S K (finiteC Γ) τ) :
    ∃ code, ActualCodeAt S K Γ τ code x := by
  refine Quot.inductionOn x ?_
  intro Q
  obtain ⟨code,_,hc,_⟩ := exact_LeastCodeSpecification S K Γ τ Q.val hk Q.property
  exact ⟨code,Q,rfl,hc⟩

theorem sameClass {S K Γ τ code} {x y : Class S K (finiteC Γ) τ}
    (hk : DecisionSourceUniverse.Closed K)
    (hx : ActualCodeAt S K Γ τ code x) (hy : ActualCodeAt S K Γ τ code y) : x = y := by
  obtain ⟨Q,hQ,heQ⟩ := hx
  obtain ⟨R,hR,heR⟩ := hy
  have eQR := (exact_LeastCodeReflectsActualQuotient S K Γ τ Q R hk).mp
    (heQ.trans heR.symm)
  exact hQ.symm.trans (eQR.trans hR)

theorem atRep {S K Γ τ code} {x : Class S K (finiteC Γ) τ}
    (hk : DecisionSourceUniverse.Closed K) (Q : WindowCarrier S K (finiteC Γ) τ)
    (hQ : classOf Q = x) (hc : ActualCodeAt S K Γ τ code x) :
    leastCode S K Γ τ Q.val = some code := by
  obtain ⟨R,hR,heR⟩ := hc
  exact ((exact_LeastCodeReflectsActualQuotient S K Γ τ Q R hk).mpr
    (hQ.trans hR.symm)).trans heR

theorem sameCode {S K Γ τ c d} {x : Class S K (finiteC Γ) τ}
    (hk : DecisionSourceUniverse.Closed K)
    (hc : ActualCodeAt S K Γ τ c x) (hd : ActualCodeAt S K Γ τ d x) : c = d := by
  obtain ⟨Q,hQ,heQ⟩ := hc
  exact Option.some.inj (heQ.symm.trans (atRep hk Q hQ hd))

theorem fibers : ExactActualClassCodeFibers := by
  intro S K Γ τ hk
  exact ⟨existsCode S K Γ τ hk,fun _ _ _ => sameClass hk,fun _ _ _ => sameCode hk⟩

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode

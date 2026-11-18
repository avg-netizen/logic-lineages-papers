import LogicLineages.PersistentMarking.HereditaryOrderTargets
import LogicLineages.PersistentMarking.DecisionPortsProof
namespace LogicLineages.PersistentMarking.HereditaryValueEqualityProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryOrderTargets

theorem refl (E : Environment) (σ : Ty) (Γ : Context) (a : Value) : ValueEq E σ Γ a a := by
  intro Δ hw he
  exact ⟨rfl,fun t ht => ⟨rfl,rfl⟩,fun ds τ hp vs hv => rfl⟩

theorem symm {E : Environment} {σ : Ty} {Γ : Context} {a b : Value} (h : ValueEq E σ Γ a b) : ValueEq E σ Γ b a := by
  intro Δ hw he
  have h := h Δ hw he
  exact ⟨h.1.symm,fun t ht => ⟨(h.2.1 t ht).1.symm,(h.2.1 t ht).2.symm⟩,
    fun ds τ hp vs hv => (h.2.2 ds τ hp vs hv).symm⟩

theorem trans {E : Environment} {σ : Ty} {Γ : Context} {a b c : Value}
    (h : ValueEq E σ Γ a b) (k : ValueEq E σ Γ b c) : ValueEq E σ Γ a c := by
  intro Δ hw he
  have h := h Δ hw he
  have k := k Δ hw he
  exact ⟨h.1.trans k.1,fun t ht => ⟨(h.2.1 t ht).1.trans (k.2.1 t ht).1,
    (h.2.1 t ht).2.trans (k.2.1 t ht).2⟩,
    fun ds τ hp vs hv => (h.2.2 ds τ hp vs hv).trans (k.2.2 ds τ hp vs hv)⟩

theorem weaken {E : Environment} {σ : Ty} {Γ Θ : Context} {a b : Value}
    (he : Extends Γ Θ) (h : ValueEq E σ Γ a b) : ValueEq E σ Θ a b := by
  intro Δ hw hd
  exact h Δ hw (DecisionPortsProof.extensionTrans Γ Θ Δ he hd)

theorem order {E : Environment} {σ : Ty} {Γ : Context} {a b c d : Value}
    (hac : ValueEq E σ Γ a c) (hbd : ValueEq E σ Γ b d) (hab : SemanticLE E σ Γ a b) :
    SemanticLE E σ Γ c d := by
  intro Δ hw he
  have hac := hac Δ hw he
  have hbd := hbd Δ hw he
  have hab := hab Δ hw he
  refine ⟨?_,?_,?_⟩
  · rw [←hac.1,←hbd.1]; exact hab.1
  · intro t ht
    rw [←(hac.2.1 t ht).1,←(hbd.2.1 t ht).1,←(hac.2.1 t ht).2,←(hbd.2.1 t ht).2]
    exact hab.2.1 t ht
  · intro ds τ hp vs hv
    rw [←hac.2.2 ds τ hp vs hv,←hbd.2.2 ds τ hp vs hv]
    exact hab.2.2 ds τ hp vs hv
end LogicLineages.PersistentMarking.HereditaryValueEqualityProof

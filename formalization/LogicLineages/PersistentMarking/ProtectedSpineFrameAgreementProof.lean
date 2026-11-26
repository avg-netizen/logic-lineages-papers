import LogicLineages.PersistentMarking.ProtectedSpineAgreementTargets
import LogicLineages.PersistentMarking.ProtectedSpineInputProof

namespace LogicLineages.PersistentMarking.ProtectedSpineFrameAgreementProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineAgreementTargets

theorem weaken (E : Environment) (C : BoundContext) (Γ Δ : Context) (a b : Assignments)
    (ha : InputValid E Γ a) (hb : InputValid E Γ b) (h : SameInputs E C Γ a b)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ) :
    SameInputs E C Δ (a.restrict E Γ Δ) (b.restrict E Γ Δ) := by
  constructor
  · intro σ x
    have hA := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ x 0 ha.1 hd he ha.2.1 ha.2.2).1
    have hB := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ b.free b.bound σ x 0 hb.1 hd he hb.2.1 hb.2.2).1
    change freeCode E Δ (weakenFree E Γ Δ a.free) σ x = freeCode E Δ (weakenFree E Γ Δ b.free) σ x
    rw [← hA,← hB,h.1 σ x]
  · intro σ i hi
    have hA := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ a.free a.bound σ 0 i ha.1 hd he ha.2.1 ha.2.2).2
    have hB := (ProtectedSpineEnvironmentNaturalProof.lookupWeakening
      E Γ Δ b.free b.bound σ 0 i hb.1 hd he hb.2.1 hb.2.2).2
    change boundCode E Δ (weakenBound E Γ Δ a.bound) σ i = boundCode E Δ (weakenBound E Γ Δ b.bound) σ i
    rw [← hA,← hB,h.2 σ i hi]

theorem push (E : Environment) (C : BoundContext) (Γ : Context) (a b : Assignments)
    (σ : Ty) (c : Code) (h : SameInputs E C Γ a b) :
    SameInputs E (C.push σ) Γ (a.push σ c) (b.push σ c) := by
  refine ⟨h.1,?_⟩
  intro ρ i hi
  cases i with
  | zero => simp [Assignments.push,boundCode,lookupBound]
  | succ i => simpa [Assignments.push,boundCode,lookupBound] using h.2 ρ i hi

theorem protectPush (C : BoundContext) (σ : Ty) (k l : Nat)
    (h : SameProtection C k l) : SameProtection (C.push σ) (k+1) (l+1) := by
  intro ρ i hi
  cases i with
  | zero => simp
  | succ i => simpa only [Nat.succ_lt_succ_iff] using h ρ i hi

end LogicLineages.PersistentMarking.ProtectedSpineFrameAgreementProof

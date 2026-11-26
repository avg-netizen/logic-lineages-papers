import LogicLineages.PersistentMarking.ProtectedSpineSoundRelationProof
import LogicLineages.PersistentMarking.MarkedConstructorLiteralProof
import LogicLineages.PersistentMarking.FiniteEqualityProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundLiteralProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation
open ProtectedSpineEnvironment (literal literalCode)

theorem literalRelated (F : Inputs S) (Γ : Context) (σ : Ty) (x : Nat)
    (hw : WellFormed F.data.types F.data.ports Γ) :
    Related F σ Γ (literalCode (domain F) Γ σ x) (some (.free σ x)) := by
  let E := domain F
  have h := HereditaryEncodeDecodeProof.encodeDecode E σ Γ (literal E σ x) hw
    (MarkedConstructorLiteralProof.literalValid E σ Γ x)
  rw [Related.eq_def]
  refine ⟨h.1,?_⟩
  intro Δ hd he
  obtain ⟨_,hBits,hApp⟩ := h.2 Δ hd he
  constructor
  · intro t ht
    obtain ⟨hWeak,hStrict⟩ := hBits t ht
    constructor
    · intro hb
      have hEq : .free σ x = t := (FiniteEqualityProof.expr _ _).mp (hWeak.symm.trans hb)
      subst t
      exact .var
    · intro hb
      exact Bool.noConfusion (hStrict.symm.trans hb)
  · intro ds τ hp xs args hx _ _ _
    have ha := hApp ds τ hp xs hx
    change (decode E σ Γ (literalCode E Γ σ x)).application Δ ds τ xs = StructuralActions.bottom E τ Δ at ha
    change Related F τ Δ ((decode E σ Γ (literalCode E Γ σ x)).application Δ ds τ xs)
      (apply (.free σ x) args)
    rw [ha]
    exact ProtectedSpineSoundRelationProof.bottomAt F τ Δ _ hd

end LogicLineages.PersistentMarking.ProtectedSpineSoundLiteralProof

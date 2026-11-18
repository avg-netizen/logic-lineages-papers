import LogicLineages.PersistentMarking.HereditaryOrderBitProof
import LogicLineages.PersistentMarking.HereditaryOrderTableProof
namespace LogicLineages.PersistentMarking.HereditaryCodeOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryOrderTargets

theorem exactOrder : CodeOrderExact := by
  intro E σ Γ a b hΓ ha hb
  have heq : (descriptor E σ).le Γ a b = codeLe E σ (canonicalLower E σ) Γ a b := by
    rw [HereditaryConstructionProof.equation]
    rfl
  rw [heq]
  unfold codeLe
  constructor
  · intro h Δ hw he
    have hd := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mpr ⟨hw,he⟩
    have h := (List.all_eq_true.mp h) Δ hd
    obtain ⟨hbits,htable⟩ := Bool.and_eq_true.mp h
    have hbitsem : ∀ k, k ∈ HereditaryOrderBitProof.bits E σ Δ →
        (HereditaryOrderBitProof.bit (HereditaryDomainSemantics.decode E σ Γ a) Δ k = true →
         HereditaryOrderBitProof.bit (HereditaryDomainSemantics.decode E σ Γ b) Δ k = true) := by
      intro k hk
      exact (HereditaryOrderBitProof.localExact E σ Γ Δ a b hw he ha hb k hk).mp
        ((List.all_eq_true.mp hbits) k hk)
    have hs := (HereditaryOrderBitProof.bitsExact E σ Δ _ _).mp hbitsem
    exact ⟨hs.1,hs.2,(HereditaryOrderTableProof.exactTable E σ Γ Δ a b hw he ha hb).mp htable⟩
  · intro h
    apply List.all_eq_true.mpr
    intro Δ hd
    obtain ⟨hw,he⟩ := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mp hd
    have h := h Δ hw he
    apply Bool.and_eq_true.mpr
    constructor
    · apply List.all_eq_true.mpr
      intro k hk
      exact (HereditaryOrderBitProof.localExact E σ Γ Δ a b hw he ha hb k hk).mpr
        ((HereditaryOrderBitProof.bitsExact E σ Δ _ _).mpr ⟨h.1,h.2.1⟩ k hk)
    · exact (HereditaryOrderTableProof.exactTable E σ Γ Δ a b hw he ha hb).mpr h.2.2
end LogicLineages.PersistentMarking.HereditaryCodeOrderProof

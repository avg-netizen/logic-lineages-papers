module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryDecodedValiditySupport
public import LogicLineages.NativeModule.PersistentMarking.HereditaryOrderTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryOrderTableProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryDecodedValiditySupport

theorem exactTable (E : Environment) (σ : Ty) (Γ Δ : Context) (a b : Code)
    (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (ha : a ∈ (descriptor E σ).carriers Γ) (hb : b ∈ (descriptor E σ).carriers Γ) :
    ((fullPrefixes σ).attach.all (fun p => (vectors (tupleBounds σ (canonicalLower E σ) Δ p)).all (fun xs =>
      match output E σ (canonicalLower E σ) Γ Δ p xs a,output E σ (canonicalLower E σ) Γ Δ p xs b with
      | some v,some w => (resultDescriptor σ (canonicalLower E σ) p).le Δ v w
      | _,_ => false)) = true ↔
      ∀ ds τ, (ds,τ) ∈ fullPrefixes σ → ∀ vs, TupleValues E Δ ds vs →
      (descriptor E τ).le Δ ((HereditaryDomainSemantics.decode E σ Γ a).application Δ ds τ vs)
        ((HereditaryDomainSemantics.decode E σ Γ b).application Δ ds τ vs) = true) := by
  constructor
  · intro h ds τ hp vs hv
    let p : Prefix σ := ⟨(ds,τ),hp⟩
    obtain ⟨xs,hxi,hxd,hxv⟩ := codeTuple E σ Δ p vs hv
    obtain ⟨x,hx,hxm⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs a hw he ha hxv
    obtain ⟨y,hy,hym⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs b hw he hb hxv
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp h) p (List.mem_attach _ _))) xs hxv
    rw [hx,hy] at h
    change (descriptor E τ).le Δ
      ((HereditaryDomainSemantics.decode E σ Γ a).application Δ p.val.1 p.val.2 vs)
      ((HereditaryDomainSemantics.decode E σ Γ b).application Δ p.val.1 p.val.2 vs) = true
    rw [decodedOutput E σ Γ Δ p a xs vs x hxi hx,decodedOutput E σ Γ Δ p b xs vs y hxi hy]
    exact h
  · intro h
    apply List.all_eq_true.mpr
    intro p hp
    apply List.all_eq_true.mpr
    intro xs hxs
    obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p xs).mp hxs
    rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hvs
    obtain ⟨hv,hi⟩ := HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 xs vs hvs
    obtain ⟨x,hx,hxm⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs a hw he ha hxs
    obtain ⟨y,hy,hym⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs b hw he hb hxs
    have h := h p.val.1 p.val.2 p.property vs hv
    rw [decodedOutput E σ Γ Δ p a xs vs x hi hx,decodedOutput E σ Γ Δ p b xs vs y hi hy] at h
    rw [hx,hy]
    exact h
end LogicLineages.PersistentMarking.HereditaryOrderTableProof

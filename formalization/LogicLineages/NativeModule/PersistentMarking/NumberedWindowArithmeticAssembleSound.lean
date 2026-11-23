module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticHeadCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAssembleSound
open NumberedWindowSyntax
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode

theorem sound (t : Nat → Option NTerm) (a : Nat → Option NArgs)
    (ts : ∀ c Q, t c = some Q → encodeTerm Q = c)
    (ars : ∀ c qs, a c = some qs → encodeArgs qs = c)
    (tag : Nat) (fields : List Nat) (Q : NTerm)
    (h : assemble t a tag fields = some Q) :
    encodeTerm Q = encodeNode tag fields := by
  unfold assemble at h
  split at h
  · obtain ⟨σ,hσ,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeTerm,NumberedWindowArithmeticTyCodeProof.decodeSound hσ]
  · obtain ⟨σ,hσ,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeTerm,NumberedWindowArithmeticTyCodeProof.decodeSound hσ]
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨σ,hσ,W,hw,rfl⟩ := h
    simp only [encodeTerm,NumberedWindowArithmeticTyCodeProof.decodeSound hσ,ts _ _ hw]
  · obtain ⟨σ,hσ,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeTerm,NumberedWindowArithmeticTyCodeProof.decodeSound hσ]
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨f,hf,bs,hbs,rfl⟩ := h
    simp only [encodeTerm,NumberedWindowArithmeticHeadCodeProof.decodeSound hf,ars _ _ hbs]
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨f,hf,τ,hτ,bs,hbs,es,hes,rfl⟩ := h
    simp only [encodeTerm,NumberedWindowArithmeticHeadCodeProof.decodeSound hf,
      NumberedWindowArithmeticTyCodeProof.decodeSound hτ,ars _ _ hbs,ars _ _ hes]
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨σ,hσ,τ,hτ,W,hw,A,ha,rfl⟩ := h
    simp only [encodeTerm,NumberedWindowArithmeticTyCodeProof.decodeSound hσ,
      NumberedWindowArithmeticTyCodeProof.decodeSound hτ,ts _ _ hw,ts _ _ ha]
  · cases h

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAssembleSound

module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationGraphTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressApplicationChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationGraphProof
open NumberedWindowApplicationGraphTargets NumberedWindowAddressApplication
open NumberedWindowAddressApplicationTargets NumberedWindowAddressApplicationChecks
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof

theorem graphExact : ExactClassApplicationGraph := by
  intro S K Γ σ τ hk q i hq argument value
  unfold graph
  rw [beq_iff_eq, exact_DecodedApplication S K]
  constructor
  · intro possible
    have guarded := possible
    unfold decodedApplication at guarded
    rw [round] at guarded
    cases hArg : decodeAddress argument with
    | none =>
        simp [hArg] at guarded
    | some u =>
        rcases u with ⟨Δ,ρ,j⟩
        simp only [hArg,Option.bind_eq_bind,Option.bind_some] at guarded
        by_cases valid : (canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ &&
            canonicalBit S K ⟨Δ,ρ,j⟩ && decide (Γ = Δ) && decide (σ = ρ)) = true
        · simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
          obtain ⟨⟨⟨_,uGood⟩,sameContext⟩,sameType⟩ := valid
          subst Δ
          subst ρ
          have argCode : encodeAddress ⟨Γ,σ,j⟩ = argument := read hArg
          obtain ⟨U,hU⟩ :=
            (NumberedWindowArithmeticAllContextAdmittedProof.canonical S K ⟨Γ,σ,j⟩ hk).mp uGood
          rw [← argCode] at possible
          obtain ⟨k,valCode,hVal⟩ :=
            (exact_ClassApplication S K Γ σ τ hk q U i j hq hU value).mp possible
          exact ⟨j,U,k,argCode.symm,hU,valCode,hVal⟩
        · simp [valid] at guarded
  · rintro ⟨j,U,k,argCode,hU,valCode,hVal⟩
    rw [argCode]
    exact (exact_ClassApplication S K Γ σ τ hk q U i j hq hU value).mpr
      ⟨k,valCode,hVal⟩

end LogicLineages.PersistentMarking.NumberedWindowApplicationGraphProof

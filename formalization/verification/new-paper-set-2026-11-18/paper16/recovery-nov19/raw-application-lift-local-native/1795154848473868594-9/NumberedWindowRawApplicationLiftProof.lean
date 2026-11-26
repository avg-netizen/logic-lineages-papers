import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessLaws

namespace LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowRawApplicationLift NumberedWindowRawApplicationLiftTargets
open NumberedWindowArithmeticFieldAlgorithmChecks NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticRawWitnessCodeChecks
open NumberedWindowArithmeticPathCheckBits NumberedWindowRawWitnessBits
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticClassAddress
open NumberedWindowTypingBits NumberedWindowTypingBitsChecks NumberedWindowPathWitnessTargets

theorem literal : ExactLiteralLift := by
  intro σ τ U Q R w
  simp only [lift, encodeTerm, encodeWitness, exact_ExactTaggedNodeCodec.1]

private theorem argumentWindow {S : Signature} {K Γ : List Ty} {σ : Ty}
    (hk : DecisionSourceUniverse.Closed K) {argument : Nat}
    {u : Class S K (finiteC Γ) σ} (hu : ActualCodeAt S K Γ σ argument u) :
    ∃ U, encodeTerm U = argument ∧ InWindow S K (finiteC Γ) σ U := by
  have canonical := (NumberedWindowArithmeticAllContextAdmittedProof.canonical
    S K ⟨Γ,σ,argument⟩ hk).mpr ⟨u,hu⟩
  cases read : decodeTerm argument with
  | none => simp [canonicalBit,read] at canonical
  | some U =>
      simp only [canonicalBit,read,Bool.and_eq_true] at canonical
      exact ⟨U,(exact_TermCodec.1 argument U).mp read,
        (exact_FiniteWindowBit S K Γ σ U).mp canonical.1⟩

theorem accepted : ExactLiftedWindowStep := by
  intro S K Γ σ τ hk u argument hu source certificate target valid
  obtain ⟨U,codeU,winU⟩ := argumentWindow hk hu
  cases readQ : decodeTerm source with
  | none => simp [windowStepCodeBit,between,readQ] at valid
  | some Q =>
    cases readW : decodeWitness certificate with
    | none => simp [windowStepCodeBit,between,readQ,readW] at valid
    | some w =>
      cases readR : decodeTerm target with
      | none => simp [windowStepCodeBit,between,readQ,readW,readR] at valid
      | some R =>
        simp only [windowStepCodeBit,between,readQ,readW,readR,
          finiteWindowWitnessBit,Bool.and_eq_true] at valid
        have winQ := (exact_FiniteWindowBit S K Γ (.arrow σ τ) Q).mp valid.1.2
        have winR := (exact_FiniteWindowBit S K Γ (.arrow σ τ) R).mp valid.2
        have winQU := NumberedWindowApplicationDomainProof.app S K (finiteC Γ) σ τ Q U hk winQ winU
        have winRU := NumberedWindowApplicationDomainProof.app S K (finiteC Γ) σ τ R U hk winR winU
        have codeQ := (exact_TermCodec.1 source Q).mp readQ
        have codeW := (exact_RawWitnessCodec.1 certificate w).mp readW
        have codeR := (exact_TermCodec.1 target R).mp readR
        dsimp only
        rw [← codeU,← codeQ,← codeW,← codeR,literal]
        simp only [windowStepCodeBit,between,exact_TermCodec.2.1,exact_RawWitnessCodec.2.1,
          finiteWindowWitnessBit,Bool.and_eq_true]
        refine ⟨⟨?_,(exact_FiniteWindowBit S K Γ τ _).mpr winQU⟩,
          (exact_FiniteWindowBit S K Γ τ _).mpr winRU⟩
        simp [rawBit,NumberedWindowRawWitnessLaws.termRefl,valid.1.1]

end LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProof

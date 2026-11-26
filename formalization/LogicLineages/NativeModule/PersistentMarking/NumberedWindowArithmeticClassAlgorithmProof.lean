module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticClassAlgorithmTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAlgorithmProof
open Spine NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowPrimaryExchangeBits NumberedWindowLiteralEquality NumberedWindowFiniteSaturation
open NumberedWindowArithmeticClassAlgorithmTargets NumberedWindowPrimaryCoverSyntax
open NumberedWindowArithmeticLeastClass NumberedWindowPrimaryClassList

private theorem originalEquality (Q R : NTerm) : (encodeTerm Q == encodeTerm R) = termEq Q R := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, NumberedWindowTypingBitsChecks.exact_LiteralTermEquality]
  constructor
  · intro h
    have e := congrArg decodeTerm h
    simpa only [exact_TermCodec.2.1,Option.some.injEq] using e
  · exact congrArg encodeTerm

private theorem originalExchange S K Γ τ Q R :
    codedExchange S K Γ τ (encodeTerm Q) (encodeTerm R) = finiteExchangeBit S K Γ τ Q R := by
  simp [codedExchange,exact_TermCodec.2.1]

theorem everyRound : ExactPrimaryRounds := by
  intro S K Γ τ vs Q n
  induction n with
  | zero =>
    simp only [NumberedWindowClassAlgorithm.rounds,rounds,List.filter_map,Function.comp_def,originalEquality]
  | succ n ih =>
    simp only [NumberedWindowClassAlgorithm.rounds,rounds,ih,NumberedWindowClassAlgorithm.advance,
      advance,List.filter_map,Function.comp_def,List.any_map,originalEquality,originalExchange]

theorem membersLeast : ExactPrimaryListAndLeast := by
  intro S K Γ τ Q
  have exactList : NumberedWindowClassAlgorithm.members (codedExchange S K Γ τ)
      ((cover S K Q).map encodeTerm) (encodeTerm Q) = (finiteClassList S K Γ τ Q).map encodeTerm := by
    have edge : finiteExchangeBit S K Γ τ = windowExchangeBit S K (NumberedWindowTypingBits.binderLookup Γ) τ := by
      funext q r; rfl
    simpa only [NumberedWindowClassAlgorithm.members, List.length_map,finiteClassList,
      classList, saturate,edge] using
      everyRound S K Γ τ (cover S K Q) Q (cover S K Q).length
  exact ⟨exactList,congrArg List.min? exactList⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAlgorithmProof

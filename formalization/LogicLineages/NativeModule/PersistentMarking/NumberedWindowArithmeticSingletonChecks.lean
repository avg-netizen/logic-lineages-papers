module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSingletonProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonChecks
open NumberedWindowArithmeticSingletonTargets NumberedWindowArithmeticSingletonProof
open NumberedWindowSingletonAlgorithm NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticSyntaxAlgorithmChecks NumberedWindowArithmeticSyntaxAlgorithmTargets

theorem exact_ExactSingletonMatrix : ExactSingletonMatrix := matrix

private theorem both {α β γ} (a : Option α) (b : Option β) (value : γ) (f : α → β → γ)
    (h : ∀ x y, a = some x → b = some y → value = f x y) :
    (if a.isSome && b.isSome then some value else none) = a.bind (fun x => b.map (f x)) := by
  cases a with
  | none => rfl
  | some x =>
    cases b with
    | none => rfl
    | some y => exact congrArg some (h x y rfl rfl)

theorem exact_ExactSingletonOutput : ExactSingletonOutput := by
  intro arg c n
  unfold output
  rw [exact_ExactTermArgsGuards arg,exact_ExactTermArgsGuards n]
  simp only [OriginalRow]
  apply Prod.ext
  · apply both
    intro a q ha hq
    rw [← (exact_TermCodec.1 arg a).mp ha,← (exact_TermCodec.1 n q).mp hq]
    simpa using term a c (encodeTerm q) q 0 (by simp)
  · apply both
    intro a qs ha hq
    rw [← (exact_TermCodec.1 arg a).mp ha,← (exact_ArgsCodec.1 n qs).mp hq]
    simpa using args a c (encodeArgs qs) qs 0 (by simp)
#print axioms exact_ExactSingletonMatrix
#print axioms exact_ExactSingletonOutput
end LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonChecks

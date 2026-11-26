module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingPushProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowBindingChecks
open NumberedWindowSyntax NumberedWindowBindingTargets
open NumberedWindowBindingBaseProof NumberedWindowBindingCancelProof NumberedWindowBindingPushProof

theorem exact_SingleCancellation : SingleCancellation := cancel
theorem exact_SingleArgsCancellation : SingleArgsCancellation := cancelArgs
theorem exact_SinglePushBlock : SinglePushBlock := push
theorem exact_SingleArgsPushBlock : SingleArgsPushBlock := pushArgs

theorem exact_OpenNumberedBeta : OpenNumberedBeta := by
  intro f σ τ k bs es a
  have hb : substituteArgs (.cons a .nil) 0 (shiftArgs 1 0 bs) = bs := by
    simpa only [Nat.zero_add,shiftArgsZero] using cancelArgs a 0 0 bs
  have he : substituteArgs (.cons a .nil) 0 (shiftArgs 1 0 es) = es := by
    simpa only [Nat.zero_add,shiftArgsZero] using cancelArgs a 0 0 es
  have hz : substituteArgs (.cons a .nil) 0 (.cons (.bound σ 0) .nil) = .cons a .nil := by
    change NArgs.cons (substitute (.cons a .nil) 0 (.bound σ 0)) .nil = .cons a .nil
    rw [substituteBoundZero]
  change NTerm.numbered f τ k (substituteArgs (.cons a .nil) 0 (shiftArgs 1 0 bs))
      (substituteArgs (.cons a .nil) 0 ((shiftArgs 1 0 es).append (.cons (.bound σ 0) .nil))) =
    .numbered f τ k bs (es.append (.cons a .nil))
  rw [substituteAppend,hb,he,hz]

#print axioms exact_SingleCancellation
#print axioms exact_SingleArgsCancellation
#print axioms exact_SinglePushBlock
#print axioms exact_SingleArgsPushBlock
#print axioms exact_OpenNumberedBeta

end LogicLineages.PersistentMarking.NumberedWindowBindingChecks

import LogicLineages.PersistentMarking.NumberedWindowBindingPushProof

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
  simp only [openNumbered,substitute,substituteAppend,hb,he,substituteArgs,substituteBoundZero]

#print axioms exact_SingleCancellation
#print axioms exact_SingleArgsCancellation
#print axioms exact_SinglePushBlock
#print axioms exact_SingleArgsPushBlock
#print axioms exact_OpenNumberedBeta

end LogicLineages.PersistentMarking.NumberedWindowBindingChecks

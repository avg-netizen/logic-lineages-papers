module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceProof
open Source Source.SourceMarkedSyntax ComparisonFreeVariables FiniteQueryPrimitives OriginalApplicationTrace

theorem exactExecutionEquation : OriginalApplicationTraceTargets.ExactExecutionEquation := OriginalApplicationTraceSupportProof.exactExecutionEquation
theorem recursiveStepFrame : OriginalApplicationTraceTargets.RecursiveStepFrame := OriginalApplicationTraceSupportProof.recursiveStepFrame

private theorem traceFrame {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Δ) {c d : Configuration Symbol arity Δ τ}
    (hc : SubtypeClosed K) (he : Execution c d) : OriginalApplicationTrace.Frame K P a c → OriginalApplicationTrace.Frame K P a d := by
  induction he with
  | refl c => intro h; exact h
  | step hn he ih => intro h; exact ih (recursiveStepFrame Symbol arity Δ τ K P a _ _ hc h hn)

theorem everyExecutionPayload : OriginalApplicationTraceTargets.EveryExecutionPayload := by
  intro Symbol arity Δ τ K P a c d hc hf he
  have hd := traceFrame K P a hc he hf
  exact ⟨hd,OriginalApplicationTraceSupportProof.payloadBounds K P a d hc hd⟩

theorem everySelectExecution : OriginalApplicationTraceTargets.EverySelectExecution := by
  intro Symbol arity Γ K P a f base extraTypes extras τ request d hc hK hP ha he
  have hp := FiniteQueryPrimitivesProof.everySelectAttemptClosure Symbol arity Γ K P a f base extraTypes extras τ request hc hK hP ha
  rcases hp with ⟨hselected,hsuffix,hτ,hqK,hqP,hqA,hargsK,hargsP,hargsA,hresult⟩
  apply everyExecutionPayload Symbol arity Γ τ K P a (ofSelect request) d hc _ he
  exact ⟨hqK,(fun {_} _ h => h),hargsK,hqP,(fun {_} _ => True.intro),hargsP,hqA,hargsA⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTraceProof

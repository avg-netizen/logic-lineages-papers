module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationProof
open OriginalHereditaryLambda OriginalHereditaryLambdaRawProof OriginalHereditaryLambdaControlProof
open OriginalHereditaryLambdaEvaluationRepeatProof OriginalHereditaryLambdaEvaluationSupportProof
open InternalOriginalUniformApplicationStepSelection
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Induction is on the actual ORIGINAL raw path code and generalized over
all four raw inputs. The child has the exact stripped certificate and the
original parameter's context field, with only its encoded Gamma extended.
The front-cons equation passes precisely the child's path, without slack. -/
theorem acceptedGuardByPath (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) :
    ∀ (code : Nat) (v : List.Vector Nat 4), (Nat.unpair (v.get 2)).1 = code →
      leafValue n arity v = 1 → evaluate (guard oldStep) v = 1 := by
  intro code
  induction code using Nat.strong_induction_on with
  | h code ih =>
    intro v hcode ha
    rcases stopValueBoolean v with hs | hs
    · obtain ⟨hm,hl,hchild⟩ := leafActiveAdvance n arity oldStep hcal v ha hs
      have hlt : (Nat.unpair ((childValues v).get 2)).1 < code := by
        simpa only [hcode] using childPathLt v hl
      have hchildLeaf : leafValue n arity (childValues v) = 1 := by
        rw [← hcal (childValues v)]
        exact hchild
      have hi := ih (Nat.unpair ((childValues v).get 2)).1 hlt (childValues v) rfl hchildLeaf
      rw [guardEvaluation] at hi ⊢
      rw [lamPathCode v hl,repeatFrontCons,transitionLiveAdvance oldStep v hs hm hl hchild]
      exact hi
    · rw [guardEvaluation,
        repeatFixed (transition oldStep) _ _ (transitionLiveStopped oldStep v hs),finishLive,hs]

theorem leafGuardAccept (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4)
    (hcal : LeafCalibrated n arity oldStep) (v : List.Vector Nat 4)
    (ha : leafValue n arity v = 1) : evaluate (guard oldStep) v = 1 :=
  acceptedGuardByPath n arity oldStep hcal (Nat.unpair (v.get 2)).1 v rfl ha

/-- Both Boolean outcomes of the unchanged original leaf are covered on
every raw input. Rejecting/malformed cases do not acquire extra premises. -/
theorem actualOriginalHereditaryLambdaRefinementEquality :
    OriginalHereditaryLambdaTargets.ActualOriginalHereditaryLambdaRefinementEquality := by
  intro n arity oldStep hcal v
  rcases OriginalConstructorLeafEvaluationProof.leafBoolean n arity v with hz | ho
  · simp [refined,conjunctionEvaluation,hcal v,hz]
  · have hg := leafGuardAccept n arity oldStep hcal v ho
    simp [refined,conjunctionEvaluation,hcal v,ho,hg]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationProof

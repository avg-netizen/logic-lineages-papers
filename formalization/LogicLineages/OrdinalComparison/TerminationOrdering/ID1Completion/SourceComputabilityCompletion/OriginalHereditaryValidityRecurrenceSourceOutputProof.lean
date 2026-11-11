module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationBoundedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceOutputProof
open InternalOriginalUniformDescentSelection (Data Calibrated)
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrence
open OriginalHereditaryValidityRecurrenceSourceRootProof
open OriginalHereditaryValidityRecurrenceSourceAcceptanceProof
open OriginalHereditaryValidityRecurrenceNumericProof
open OriginalHereditaryValidityEvaluationBoundedProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full-output equality, including every malformed or rejected root. This
uses the bounded machine recurrence, not a substitute source predicate. -/
theorem calibratedValidatorOutput (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (v : List.Vector Nat 2) :
    evaluate (validator data.oldSource data.oldTarget data.member) v =
      evaluate data.oldSource v := by
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1] := List.Vector.ext fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i <;> rfl
  rw [hv,validatorEvaluation]
  let source : Nat → Nat → Nat :=
    fun value parameter => evaluate data.oldSource (List.Vector.ofFn ![value,parameter])
  let target : Nat → Nat → Nat :=
    fun value parameter => evaluate data.oldTarget (List.Vector.ofFn ![value,parameter])
  let member : Nat → Nat → Nat :=
    fun value parameter => evaluate data.member (List.Vector.ofFn ![value,parameter])
  change validatorValue source target member (v.get 0) (v.get 1) = source (v.get 0) (v.get 1)
  have hb : source (v.get 0) (v.get 1) = 0 ∨ source (v.get 0) (v.get 1) = 1 := by
    simpa only [source,hc.1] using
      sourceBoolean n arity (List.Vector.ofFn ![v.get 0,v.get 1])
  have hr := actualOriginalHereditaryValidatorRecurrence source target member (v.get 0) (v.get 1)
  rcases hb with hs | hs
  · rcases hr.1 with hz | ho
    · exact hz.trans hs.symm
    · have hn := (hr.2.mp ho).1
      simp only [nodeCheckValue,hs,Nat.zero_ne_one,if_false] at hn
  · have hs' : InternalOriginalUniformParameterLeaves.sourceValue n arity
        (List.Vector.ofFn ![v.get 0,v.get 1]) = 1 :=
      (hc.1 _).symm.trans hs
    have ht := sourceTyped n arity (v.get 0) (v.get 1) hs'
    exact (typedValidator n arity data hc (Nat.unpair (v.get 1)).1 _ ht).trans hs.symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceOutputProof

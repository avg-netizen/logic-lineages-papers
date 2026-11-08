module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationMeaningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSemanticProof
open Source InternalRepresentativeFoldCalibration InternalApplicationValidityStack
open InternalApplicationResultFoldCalibration InternalOriginalStepGuard InternalQuotientEdgeChecker
open InternalRepresentativeFoldCalibrationSupportProof InternalApplicationValidityStackStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Induction is on the original input payload. Computed representative sizes
never enter it, and rejected/nonapplication roots use the whole-input leaf. -/
theorem actualOriginalSemanticRepresentativeFoldCalibration :
    InternalRepresentativeFoldCalibrationTargets.ActualOriginalSemanticRepresentativeFoldCalibration := by
  intro n arity symbols S Gamma table validity member old hc hv hm ho value
  let G : Nat → Nat := fun x => evaluate (rootGuard validity member) (List.Vector.ofFn ![x])
  let L : Nat → Nat := fun x =>
    evaluate (InternalRepresentativeFoldCalibration.leaf validity member old) (List.Vector.ofFn ![x])
  let C : Nat → Nat → Nat → Nat → Nat := fun d e f a =>
    evaluate (combine old) (List.Vector.ofFn ![d,e,f,a])
  change semanticFold G L C value = targetRepresentativeValue n arity symbols S Gamma value
  have hG (x : Nat) : G x = sourceValidityValue n arity symbols S Gamma x :=
    rootGuardCalibration n arity symbols S Gamma validity member hv hm (List.Vector.ofFn ![x])
  have hL (x : Nat) : L x = targetRepresentativeValue n arity symbols S Gamma x :=
    leafCalibration n arity symbols S Gamma table validity member old hv hm ho (List.Vector.ofFn ![x])
  suffices allPayloads : ∀ bound value : Nat, payloadValue value = bound →
      semanticFold G L C value = targetRepresentativeValue n arity symbols S Gamma value by
    exact allPayloads (payloadValue value) value rfl
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro value hbound
    rw [InternalApplicationResultFoldCalibrationMeaningProof.actualOriginalSemanticResultFoldEquation]
    by_cases hop : tagValue value = 2 ∧ G value = 1
    · rw [if_pos hop]
      have hb := applicationPayloadBound value hop.1
      have hf : payloadValue (functionChildValue value) < bound := by
        rw [functionChildPayload]
        omega
      have ha : payloadValue (argumentChildValue value) < bound := by
        rw [argumentChildPayload]
        omega
      rw [ih (payloadValue (functionChildValue value)) hf (functionChildValue value) rfl,
        ih (payloadValue (argumentChildValue value)) ha (argumentChildValue value) rfl]
      exact openedRootCombine n arity symbols S hc Gamma table old ho value hop.1
        ((hG value).symm.trans hop.2)
    · rw [if_neg hop]
      exact hL value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSemanticProof

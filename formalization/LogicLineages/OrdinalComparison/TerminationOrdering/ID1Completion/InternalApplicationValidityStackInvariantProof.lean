module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInvariantProof
open Source InternalApplicationValidityStack InternalOriginalStepGuard

theorem applicationReconstruction (value : Nat) (h : tagValue value = 2) :
    applicationValue (domainValue value) (resultTypeValue value)
      (functionPayloadValue value) (argumentPayloadValue value) = value := by
  calc
    _ = Nat.pair (resultTypeValue value) (Nat.pair (tagValue value) (bodyValue value)) := by
      simp only [applicationValue, domainValue, functionPayloadValue, argumentPayloadValue,
        Nat.pair_unpair, h]
    _ = value := by
      simp only [resultTypeValue, tagValue, bodyValue, payloadValue, Nat.pair_unpair]

theorem stepInvariant (node valid : Nat → Nat)
    (app : ∀ value : Nat, tagValue value = 2 →
      (valid value = 1 ↔ node (resultTypeValue value) = 1 ∧
        valid (functionChildValue value) = 1 ∧ valid (argumentChildValue value) = 1))
    (state : State) :
    stateValid valid (stateStep node valid state) ↔ stateValid valid state := by
  rcases state with ⟨s, xs⟩
  by_cases hs : s = 1
  · subst s
    cases xs with
    | nil => simp [stateStep, stateValid]
    | cons value rest =>
      by_cases ht : tagValue value = 2
      · have hv := app value ht
        by_cases hn : node (resultTypeValue value) = 1 <;>
          simp [stateStep, stateValid, failedState, ht, hn, hv, and_assoc]
      · by_cases hv : valid value = 1 <;>
          simp [stateStep, stateValid, failedState, ht, hv]
  · simp [stateStep, stateValid, failedState, hs]

theorem targetAppAcceptance (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) (h : tagValue value = 2) :
    targetValidityValue n arity Gamma value = 1 ↔
      (fun _ : Nat => 1) (resultTypeValue value) = 1 ∧
      targetValidityValue n arity Gamma (functionChildValue value) = 1 ∧
      targetValidityValue n arity Gamma (argumentChildValue value) = 1 := by
  have he := (InternalApplicationValidityStackDecoderProof.actualOriginalApplicationDecoderEquations
    n arity [] [] Gamma (domainValue value) (resultTypeValue value)
      (functionPayloadValue value) (argumentPayloadValue value)).1
  rw [applicationReconstruction value h] at he
  change targetValidityValue n arity Gamma value =
    (if targetValidityValue n arity Gamma (functionChildValue value) = 1 ∧
      targetValidityValue n arity Gamma (argumentChildValue value) = 1 then 1 else 0) at he
  rw [he]
  simp

theorem sourceAppAcceptance (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat) (h : tagValue value = 2) :
    sourceValidityValue n arity symbols S Gamma value = 1 ↔
      InternalStructuralEndpointGuard.membershipValue S (resultTypeValue value) = 1 ∧
      sourceValidityValue n arity symbols S Gamma (functionChildValue value) = 1 ∧
      sourceValidityValue n arity symbols S Gamma (argumentChildValue value) = 1 := by
  have he := (InternalApplicationValidityStackDecoderProof.actualOriginalApplicationDecoderEquations
    n arity symbols S Gamma (domainValue value) (resultTypeValue value)
      (functionPayloadValue value) (argumentPayloadValue value)).2
  rw [applicationReconstruction value h] at he
  change sourceValidityValue n arity symbols S Gamma value =
    (if InternalStructuralEndpointGuard.membershipValue S (resultTypeValue value) = 1 ∧
      sourceValidityValue n arity symbols S Gamma (functionChildValue value) = 1 ∧
      sourceValidityValue n arity symbols S Gamma (argumentChildValue value) = 1 then 1 else 0) at he
  rw [he]
  simp

theorem actualOriginalStackValidityInvariant :
    InternalApplicationValidityStackTargets.ActualOriginalStackValidityInvariant := by
  intro n arity symbols S Gamma state
  exact ⟨stepInvariant _ _ (targetAppAcceptance n arity Gamma) state,
    stepInvariant _ _ (sourceAppAcceptance n arity symbols S Gamma) state⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInvariantProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInvariantProof

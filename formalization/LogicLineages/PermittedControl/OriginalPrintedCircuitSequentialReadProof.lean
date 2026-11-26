module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialTargets
import LogicLineages.PermittedControl.OriginalMixedGateSequentialReadProof
import LogicLineages.PermittedControl.OriginalNaturalFieldGatesProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitSequential
open FieldComparison (ClosedNaturalFieldResult)

private theorem baseHit (r : Option Nat) (v : Nat) : baseResult r = .ok v ↔ r = some v := by
  cases r <;> simp [baseResult]

private theorem fieldHit (r : ClosedNaturalFieldResult) (v : Nat) :
    fieldResult r = .ok v ↔ r = some (some v) := by
  cases r with
  | none => simp [fieldResult]
  | some h => cases h <;> simp [fieldResult]

private theorem fieldInvalid (r : ClosedNaturalFieldResult) :
    fieldResult r = .error .invalidField ↔ r = none := by
  cases r with
  | none => simp [fieldResult]
  | some h => cases h <;> simp [fieldResult]

private theorem fieldMiss (r : ClosedNaturalFieldResult) :
    fieldResult r = .error .missedField ↔ r = some none := by
  cases r with
  | none => simp [fieldResult]
  | some h => cases h <;> simp [fieldResult]

theorem exactCircuitGateReads : ExactCircuitGateReads := by
  refine ⟨?_,?_,?_⟩
  · intro f g θ
    cases g with
    | base g =>
        exact (baseHit (g.read f θ) (θ g.output)).trans
          (OriginalMixedGateSequential.exactMixedGateRead.1 f θ g)
    | field g =>
        exact (fieldHit (g.read f θ) (θ g.output)).trans
          (OriginalNaturalFieldGates.exactOrdinarySharedGateGraph f g θ θ).1
  · intro f g base final hInputs
    cases g with
    | base g =>
        exact congrArg baseResult (OriginalMixedGateSequential.readCongruent f g base final hInputs)
    | field g =>
        exact congrArg fieldResult
          ((OriginalNaturalFieldGates.exactOrdinarySharedGateGraph f g base final).2 hInputs).1
  · intro f g θ
    have facts := OriginalNaturalFieldGates.exactOrdinaryGateReads f g (θ g.source)
    exact ⟨(fieldInvalid (g.read f θ)).trans facts.1,(fieldMiss (g.read f θ)).trans facts.2.1⟩

end LogicLineages.PermittedControl.OriginalPrintedCircuitSequential

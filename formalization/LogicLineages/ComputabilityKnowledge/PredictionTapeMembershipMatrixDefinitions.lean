module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionMaximumDefinitions
@[expose] public section
/-! Source paper14 lem:membership. The witness gives a cutoff and a common
finite certificate for binary halting below it. A query gives an input and
a stage of the ordinary total bound program. Its computed VALUE is used as
the strict ordinary tape budget. The bound-program evaln stage is never
identified with the evader's tape runtime. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrix
open PredictionTapeObservation

def finiteCheck (code cutoff fuel : Nat) : Bool :=
  (List.range (cutoff + 1)).all fun n =>
    (PredictionCommonFuel.booleanHistories n).all fun xs => (boundedMove code fuel xs).isSome

def guardedCheck (code : Nat) (bound : Nat.Partrec.Code) (cutoff : Nat) (xs : List Bool) (stage : Nat) : Bool :=
  if cutoff < xs.length then
    match Nat.Partrec.Code.evaln stage bound xs.length with
    | none => true
    | some v => (boundedMove code v xs).isSome
  else true

def membershipMatrix (code : Nat) (bound : Nat.Partrec.Code) (witness query : Nat) : Bool :=
  finiteCheck code witness.unpair.1 witness.unpair.2 &&
    guardedCheck code bound witness.unpair.1
      ((Encodable.decode (α := List Bool) query.unpair.1).getD []) query.unpair.2

end LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrix

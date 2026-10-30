module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatch
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluation
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCode

@[expose] public section
/-! Immutable extension with arithmetic-only evaluation and full closed-term
simultaneous substitution. Other U/u dispatch is preserved, but arbitrary
formulas and revision extensions are not identified with the previous ground. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry
open GorbowRegistryDecoder

def tupleSubstitute (n code packed : Nat) : Option Nat := do
  let codes ← decodeTuple packed
  GorbowSortedSimultaneousCode.substituteNumber n code codes

def functionProgram (code : Nat) : Nat :=
  match decodeHeader code with
  | none => GorbowSortedRegistry.functionProgram code
  | some (arity,tag,args) =>
    if arity=1 ∧ tag=1 ∧ args.length=1 then
      (GorbowArithmeticEvaluation.sortedValue (args.getD 0 0)).getD 0
    else if arity=3 ∧ tag=1 ∧ args.length=3 then
      (tupleSubstitute (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)).getD 0
    else GorbowSortedRegistry.functionProgram code

def ground : GorbowSortedRevision.Ground :=
  ⟨GorbowSortedRegistry.ground.universalRelation,functionProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry

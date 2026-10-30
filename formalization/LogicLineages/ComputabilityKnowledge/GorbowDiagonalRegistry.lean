module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplication
public import LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistry

@[expose] public section
/-! Fresh immutable registry with a sorted self-application function tag.
Old/new full-language interpretations are not identified. This stage supplies
an actual executable function, not a logical diagonal theorem. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistry
open GorbowRegistryDecoder

def functionProgram (code : Nat) : Nat :=
  match decodeHeader code with
  | none => GorbowAtomicRegistry.functionProgram code
  | some (arity,tag,args) =>
    if arity=1 ∧ tag=2 ∧ args.length=1 then
      (GorbowSortedSelfApplication.selfApply (args.getD 0 0)).getD 0
    else GorbowAtomicRegistry.functionProgram code

def ground : GorbowSortedRevision.Ground :=
  ⟨GorbowSortedRegistry.ground.universalRelation,functionProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistry

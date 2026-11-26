module

public import LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowPositivePathAlgorithm List.Vector

abbrev StepInput := List Nat × Nat × Nat × Nat × Nat
abbrev LeastInput := List Nat × Nat × Nat
abbrev PathInput := List Nat × Nat × Nat × Nat × Nat
abbrev AddressInput := Nat × Nat × Nat

def PositivePathPrograms : Prop :=
  ∀ (step : Step) (least : Least),
    Primrec (fun p : StepInput => step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) →
    Primrec (fun p : LeastInput => least p.1 p.2.1 p.2.2) →
    (∃ p : GorbowPRProgram.Program 1, ∀ ctx ty source cert target,
      GorbowPRProgram.evaluate p (Encodable.encode ((ctx,ty,source,cert,target) : PathInput) ::ᵥ List.Vector.nil) =
        (if positive step least ctx ty source cert target then 1 else 0)) ∧
    (∃ p : GorbowPRProgram.Program 3, ∀ source cert target,
      GorbowPRProgram.evaluate p (source ::ᵥ cert ::ᵥ target ::ᵥ List.Vector.nil) =
        (if addressRS step least source cert target then 1 else 0))

end LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramTargets

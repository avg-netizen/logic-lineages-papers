module

public import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawContextProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowRawContextAlgorithm List.Vector

abbrev WindowInput := List Nat × Nat × Nat
abbrev StepInput := List Nat × Nat × Nat × Nat × Nat

def ContextualStepProgram : Prop :=
  ∀ (root : RawRoot) (window : Window),
    Primrec (fun p : Frame => root p.1 p.2.1 p.2.2) →
    Primrec (fun p : WindowInput => window p.1 p.2.1 p.2.2) →
    ∃ p : GorbowPRProgram.Program 1, ∀ ctx ty q w r,
      GorbowPRProgram.evaluate p (Encodable.encode ((ctx,ty,q,w,r) : StepInput) ::ᵥ List.Vector.nil) =
        (if windowStep root window ctx ty q w r then 1 else 0)

end LogicLineages.PersistentMarking.NumberedWindowRawContextProgramTargets

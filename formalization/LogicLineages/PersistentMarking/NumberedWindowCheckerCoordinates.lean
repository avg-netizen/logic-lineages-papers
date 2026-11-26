module
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinates
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

def domain (p : Program 1) : Program 2 :=
  .composition p (fun _ => .projection 1)

def suppliedCertificate (p : Program 3) : Program 4 :=
  .composition p (Fin.cases (.projection 1) (Fin.cases (.projection 3) (fun _ => .projection 2)))

def ExactCoordinates : Prop :=
  (∀ (p : Program 1) (c n : Nat),
    evaluate (domain p) (c ::ᵥ n ::ᵥ nil) = evaluate p (n ::ᵥ nil)) ∧
  (∀ (p : Program 3) (c src dst cert : Nat),
    evaluate (suppliedCertificate p) (c ::ᵥ src ::ᵥ dst ::ᵥ cert ::ᵥ nil) =
      evaluate p (src ::ᵥ cert ::ᵥ dst ::ᵥ nil))
end LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinates

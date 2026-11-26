module

public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowClassAlgorithm List.Vector

abbrev ExchangeInput := Nat × Nat × Nat × Nat

def ClassPrograms : Prop := ∀ (cover : Nat → List Nat) (edge : Nat → Nat → Nat → Nat → Bool),
  Primrec cover → Primrec (fun p : ExchangeInput => edge p.1 p.2.1 p.2.2.1 p.2.2.2) →
  (∃ p : GorbowPRProgram.Program 3, ∀ ctx ty seed,
    GorbowPRProgram.evaluate p (ctx ::ᵥ ty ::ᵥ seed ::ᵥ List.Vector.nil) =
      Encodable.encode (members (edge ctx ty) (cover seed) seed)) ∧
  (∃ p : GorbowPRProgram.Program 3, ∀ ctx ty seed,
    GorbowPRProgram.evaluate p (ctx ::ᵥ ty ::ᵥ seed ::ᵥ List.Vector.nil) =
      Encodable.encode (least (edge ctx ty) (cover seed) seed))

end LogicLineages.PersistentMarking.NumberedWindowClassProgramTargets

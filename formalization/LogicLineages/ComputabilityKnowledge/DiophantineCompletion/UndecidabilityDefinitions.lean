module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Undecidability

/-- Halting of the actual ordinary code on zero, transported to Nat by the
existing code decoder. This is the RE halting predicate, not its complement. -/
def natHaltsZero (e : Nat) : Prop :=
  (Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode e) 0).Dom

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Undecidability

module
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBlankHaltingUniversality.Targets

def ExactSpecialization : Prop :=
  Primrec₂ specialize ∧ ∀ (c : Nat.Partrec.Code) (n x : Nat),
    (specialize c n).eval x=c.eval n

def UniformTranslator : Prop := ∃ U : Turing.ToPartrec.Code,
  Primrec (fun p : Nat.Partrec.Code × Nat => output U p.1 p.2) ∧
  ∀ (c : Nat.Partrec.Code) (n : Nat),
    SourceBlankMachineSimulation.Halts (output U c n) ↔ (c.eval n).Dom

def REUniversality : Prop := ∀ P : Nat → Prop, REPred P →
  (∃ f : Nat → Nat, Primrec f ∧ ∀ n,
    P n ↔ SourceBlankMachineSimulation.Halts (f n)) ∧
  ManyOneReducible P SourceBlankMachineSimulation.Halts
end LogicLineages.OrdinalComparison.Source.SourceBlankHaltingUniversality.Targets

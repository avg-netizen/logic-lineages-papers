module
public import LogicLineages.OrdinalComparison.SourceGammaCoREClassificationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCoREClassification.Targets

def REComplement : Prop := ∀ b : Nat, REPred (fun code => ¬language b code)

def UniversalCoRE : Prop := ∀ (b : Nat) (P : Nat → Prop),
  REPred (fun n => ¬P n) → ManyOneReducible P (language b)

def ReversePrimitiveReduction : Prop := ∀ b : Nat,
  ∃ f : Nat → Nat, Primrec f ∧ ∀ code,
    language b code ↔ nonhalting (f code)

def ExactManyOneEquivalence : Prop := ∀ b : Nat,
  ManyOneEquiv (language b) nonhalting
end LogicLineages.OrdinalComparison.Source.SourceGammaCoREClassification.Targets

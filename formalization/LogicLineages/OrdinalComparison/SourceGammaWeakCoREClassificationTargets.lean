module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCoREClassificationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCoREClassification.Targets

def REComplement : Prop := ∀ b : Nat, REPred (fun code => ¬language b code)

def UniversalCoRE : Prop := ∀ (b : Nat) (P : Nat → Prop),
  REPred (fun n => ¬P n) → ManyOneReducible P (language b)

def ReversePrimitiveReduction : Prop := ∀ b : Nat,
  ∃ f : Nat → Nat, Primrec f ∧ ∀ code,
    language b code ↔ nonhalting (f code)

def ExactManyOneEquivalence : Prop := ∀ b : Nat,
  ManyOneEquiv (language b) nonhalting
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCoREClassification.Targets

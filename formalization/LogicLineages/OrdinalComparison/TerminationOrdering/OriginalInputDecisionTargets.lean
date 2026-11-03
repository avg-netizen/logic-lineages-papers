module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionTargets
open Source FiniteObservationBits OriginalInputDecision

def RootReadAdequacy : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
    (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop)
    (_ : DecidableRel above),
  (compare I above false=true ↔ OriginalWeak I above) ∧
  (compare I above true=true ↔ OriginalStrict I above)

def WrongTypeRejection : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
    (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop)
    (_ : DecidableRel above), I.sourceType≠I.targetType →
  compare I above false=false ∧ compare I above true=false ∧
    ¬ OriginalWeak I above ∧ ¬ OriginalStrict I above

/-- Actual constructive decision data, not merely classical existence of a
decision procedure. These deciders are to branch on the above literal Bool. -/
def OriginalComparisonsDecidable : Type 1 := ∀ (Symbol : Type) (_ : DecidableEq Symbol)
    (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop)
    (_ : DecidableRel above), Decidable (OriginalWeak I above) × Decidable (OriginalStrict I above)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionTargets

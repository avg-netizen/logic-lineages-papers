module

public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution.Targets
open GorbowSyntax GorbowPACore GorbowFormulaSubstitution GorbowTheoryProof

def InstantiationNaturality : Prop := ∀ n m (sigma : Fin n → Term m)
  (a : Formula (n + 1)) (t : Term n),
  substituteFormula sigma (GorbowStandardInstances.instantiate a t) =
    GorbowStandardInstances.instantiate (substituteFormula (liftSubstitute sigma) a)
      (GorbowSubstitution.substitute sigma t)

def LogicalInstances : Prop := ∀ n m (sigma : Fin n → Term m) (w : LogicalInstance n),
  substituteFormula sigma (logicalFormula w) = logicalFormula (logicalMap sigma w)

def ArithmeticInstances : Prop := ∀ n m (sigma : Fin n → Term m) (w : ArithmeticInstance n),
  substituteFormula sigma (arithmeticFormula w) = arithmeticFormula (arithmeticMap sigma w)

/-- Every actual existing proof transports under arbitrary simultaneous
substitution, including full-language terms and all induction instances. -/
def DerivationSubstitution : Prop := ∀ (A : Sentence → Prop) n m (a : Formula n)
  (sigma : Fin n → Term m), Nonempty (Derivation A a) →
  Nonempty (Derivation A (substituteFormula sigma a))

def ClosedLifting : Prop := ∀ (A : Sentence → Prop) (a : Sentence),
  Nonempty (Derivation (n := 0) A a) → ∀ n,
  Nonempty (Derivation A (weakenClosed n a))

def Target : Prop := InstantiationNaturality ∧ LogicalInstances ∧ ArithmeticInstances ∧
  DerivationSubstitution ∧ ClosedLifting

end LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution.Targets

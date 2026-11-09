module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsDefinitions

@[expose] public section
/-! Proof-free arithmetic interpretation for a possible actual proof-calculus
transfer. The ONE inductive body is arithmetic falsum and its predicate is
also interpreted as falsum. No ID1 closure/leastness axiom enters Gorbow PA.
Mathlib bound variables are levels; the new Gorbow bound variable is zero. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer
open GorbowSyntax
open LogicLineages.OrdinalComparison.TerminationOrdering

abbrev SourceFormula (alpha : Type) := PositiveArithmeticOperators.language.Formula alpha
abbrev SourceTerm (alpha : Type) := PositiveArithmeticOperators.language.Term alpha

def falseBody : PositiveArithmeticOperators.Positive (Fin 1) :=
  .arithmetic (.falsum : OrdinaryArithmetic.Formula (Fin 1))

def falsity {n : Nat} : Formula n := .neg (.equal .zero .zero)

def translateTerm {alpha : Type} {m : Nat} (rho : alpha → Term m) : SourceTerm alpha → Term m
  | .var i => rho i
  | .func .zero _ => .zero
  | .func .succ ts => .succ (translateTerm rho (ts 0))
  | .func .add ts => .add (translateTerm rho (ts 0)) (translateTerm rho (ts 1))
  | .func .mul ts => .mul (translateTerm rho (ts 0)) (translateTerm rho (ts 1))

def translateBounded {alpha : Type} : {l m : Nat} →
    PositiveArithmeticOperators.language.BoundedFormula alpha l →
      (alpha → Term m) → (Fin l → Term m) → Formula m
  | _, _, .falsum, _, _ => falsity
  | _, _, .equal t u, rho, beta =>
      .equal (translateTerm (Sum.elim rho beta) t) (translateTerm (Sum.elim rho beta) u)
  | _, _, .rel _ _, _, _ => falsity
  | _, _, .imp a b, rho, beta =>
      .imp (translateBounded a rho beta) (translateBounded b rho beta)
  | _, _, .all a, rho, beta => .all (translateBounded a
      (fun i => GorbowFormulaSubstitution.renameTerm Fin.succ (rho i))
      (Fin.lastCases (.var 0)
        (fun i => GorbowFormulaSubstitution.renameTerm Fin.succ (beta i))))

def translate {alpha : Type} {m : Nat} (phi : SourceFormula alpha) (rho : alpha → Term m) : Formula m :=
  translateBounded phi rho Fin.elim0

/-- Every finite local assumption is discharged in its original order. -/
def closeAssumptions {n : Nat} (Gamma : List (Formula n)) (phi : Formula n) : Formula n :=
  Gamma.foldr Formula.imp phi

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer

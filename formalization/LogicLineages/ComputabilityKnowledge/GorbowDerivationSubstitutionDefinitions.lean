module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
/-! Actual substitution maps of the existing logical/arithmetic axiom
instances. These are finite syntax transformations, not new proof rules.
Proof transport must still be constructed in the unchanged Hilbert calculus. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution
open GorbowSyntax GorbowPACore GorbowFormulaSubstitution

def logicalMap {n m : Nat} (sigma : Fin n → Term m) : LogicalInstance n → LogicalInstance m
  | .k a b => .k (substituteFormula sigma a) (substituteFormula sigma b)
  | .s a b c => .s (substituteFormula sigma a) (substituteFormula sigma b)
      (substituteFormula sigma c)
  | .classicalContraposition a b =>
      .classicalContraposition (substituteFormula sigma a) (substituteFormula sigma b)
  | .andLeft a b => .andLeft (substituteFormula sigma a) (substituteFormula sigma b)
  | .andRight a b => .andRight (substituteFormula sigma a) (substituteFormula sigma b)
  | .andIntro a b => .andIntro (substituteFormula sigma a) (substituteFormula sigma b)
  | .orLeft a b => .orLeft (substituteFormula sigma a) (substituteFormula sigma b)
  | .orRight a b => .orRight (substituteFormula sigma a) (substituteFormula sigma b)
  | .orElim a b c => .orElim (substituteFormula sigma a) (substituteFormula sigma b)
      (substituteFormula sigma c)
  | .existsDualForward a => .existsDualForward (substituteFormula (liftSubstitute sigma) a)
  | .existsDualBackward a => .existsDualBackward (substituteFormula (liftSubstitute sigma) a)
  | .reflexive t => .reflexive (GorbowSubstitution.substitute sigma t)
  | .equalityReplace a t u => .equalityReplace (substituteFormula (liftSubstitute sigma) a)
      (GorbowSubstitution.substitute sigma t) (GorbowSubstitution.substitute sigma u)
  | .allInstantiate a t => .allInstantiate (substituteFormula (liftSubstitute sigma) a)
      (GorbowSubstitution.substitute sigma t)
  | .allDistribute a b => .allDistribute (substituteFormula (liftSubstitute sigma) a)
      (substituteFormula (liftSubstitute sigma) b)
  | .allVacuous a => .allVacuous (substituteFormula sigma a)

def arithmeticMap {n m : Nat} (sigma : Fin n → Term m) :
    ArithmeticInstance n → ArithmeticInstance m
  | .succNotZero t => .succNotZero (GorbowSubstitution.substitute sigma t)
  | .succInjective t u => .succInjective (GorbowSubstitution.substitute sigma t)
      (GorbowSubstitution.substitute sigma u)
  | .addZero t => .addZero (GorbowSubstitution.substitute sigma t)
  | .addSucc t u => .addSucc (GorbowSubstitution.substitute sigma t)
      (GorbowSubstitution.substitute sigma u)
  | .mulZero t => .mulZero (GorbowSubstitution.substitute sigma t)
  | .mulSucc t u => .mulSucc (GorbowSubstitution.substitute sigma t)
      (GorbowSubstitution.substitute sigma u)
  | .induction a => .induction (substituteFormula (liftSubstitute sigma) a)

end LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution

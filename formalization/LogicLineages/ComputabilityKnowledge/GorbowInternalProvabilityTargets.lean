module

public import LogicLineages.ComputabilityKnowledge.GorbowInternalProvabilityDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowInternalProvability.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowTheoryChecker

def CheckerProgram : Prop :=
  ∀ axCheck : List Nat → Bool, Primrec axCheck →
    ∃ p : Program 2, Represents axCheck p

def LiteralSubstitution : Prop := ∀ formula : Nat,
  GorbowStandardInstances.instantiate provabilityFormula (Term.numeral formula) =
    atCode formula

def NumeralCertification : Prop := ∀ (p : Program 2) (formula certificate : Nat),
  evaluate p (arguments formula certificate) = 1 →
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (atCode formula))

def ExactStandardSemantics : Prop :=
  ∀ (axCheck : List Nat → Bool) (p : Program 2), Represents axCheck p →
    ∀ (I : Interpretation) (formula : Nat),
      Formula.realize (GorbowPRDefiningEquations.interpretation p I)
        Fin.elim0 (atCode formula) ↔
      ∃ phi : Sentence, formula = GorbowSortedSyntaxCode.formulaCode phi ∧
        Nonempty (Derivation (ProgramTheory axCheck) phi)

def InternalCertification : Prop :=
  ∀ axCheck : List Nat → Bool, Primrec axCheck →
    ∃ p : Program 2, Represents axCheck p ∧
      ∀ phi : Sentence, Nonempty (Derivation (ProgramTheory axCheck) phi) →
        Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
          (atCode (GorbowSortedSyntaxCode.formulaCode phi)))

def Target : Prop := CheckerProgram ∧ LiteralSubstitution ∧
  NumeralCertification ∧ ExactStandardSemantics ∧ InternalCertification

end LogicLineages.ComputabilityKnowledge.GorbowInternalProvability.Targets

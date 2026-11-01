module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

def PreservesEvaluation : Prop := ∀ n (p : Program 1) (q : Program n) (v : List.Vector Nat 1),
  evaluate (augment p q) v = evaluate p v

def ExactCheckerTag : Prop := ∀ n (p pR : Program 1) (q : Program n),
  (nodes (GorbowSourceRegistryPadding.root (augment p q) pR))[checkerTag p]? = some ⟨n,q⟩

def PreservesCalibration : Prop := ∀ n (pF pR : Program 1) (q : Program n),
  GorbowSelectedDistribution.Calibrated pF pR →
    GorbowSelectedDistribution.Calibrated (augment pF q) pR

def NumeralCertificates : Prop := ∀ n (pF pR : Program 1) (q : Program n)
    (v : List.Vector Nat n),
  Nonempty (Derivation (n := 0) (GorbowNamedDefiningTheory.Theory (augment pF q) pR)
    (.equal (GorbowPRDefiningEquations.call (checkerTag pF)
      (GorbowPRNumeralCalculation.numeralArguments v)) (Term.numeral (evaluate q v)))) ∧
  ∀ value, evaluate q v ≠ value →
    Nonempty (Derivation (n := 0) (GorbowNamedDefiningTheory.Theory (augment pF q) pR)
      (.neg (.equal (GorbowPRDefiningEquations.call (checkerTag pF)
        (GorbowPRNumeralCalculation.numeralArguments v)) (Term.numeral value))))

def LiteralSubstitution : Prop := ∀ tag formula,
  GorbowStandardInstances.instantiate (provabilityFormula tag) (Term.numeral formula) =
    atCode tag formula

/-- A concrete named base contains the checker and proves each actual external
proof's existential certificate. The checked theory need not equal that base. -/
def NamedInternalization : Prop := ∀ axCheck : List Nat → Bool, Primrec axCheck →
  ∃ (pF pR : Program 1) (q : Program 2),
    GorbowSelectedDistribution.Calibrated (augment pF q) pR ∧
    GorbowInternalProvability.Represents axCheck q ∧
    ∀ sigma : Sentence, Nonempty (Derivation (GorbowTheoryChecker.ProgramTheory axCheck) sigma) →
      Nonempty (Derivation (GorbowNamedDefiningTheory.Theory (augment pF q) pR)
        (atCode (checkerTag pF) (GorbowSortedSyntaxCode.formulaCode sigma)))

/-- Actual finite registry semantics, without identifying it with a different
old full-language ground or assuming source DCB adequacy. -/
def ExactStandardSemantics : Prop := ∀ (axCheck : List Nat → Bool) (q : Program 2),
  GorbowInternalProvability.Represents axCheck q → ∀ (pF pR : Program 1) I formula,
  (atCode (checkerTag pF) formula).realize
    (GorbowNamedRegistryInterpretation.interpretation (augment pF q) pR I) Fin.elim0 ↔
  ∃ sigma : Sentence, formula = GorbowSortedSyntaxCode.formulaCode sigma ∧
    Nonempty (Derivation (GorbowTheoryChecker.ProgramTheory axCheck) sigma)

def Target : Prop := PreservesEvaluation ∧ ExactCheckerTag ∧ PreservesCalibration ∧
  NumeralCertificates ∧ LiteralSubstitution ∧ NamedInternalization ∧ ExactStandardSemantics

end LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability.Targets

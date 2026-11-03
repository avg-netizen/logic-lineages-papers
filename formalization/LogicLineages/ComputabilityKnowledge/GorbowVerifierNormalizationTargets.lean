module

public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

def ActualEvaluation : Prop :=
  (∀ x : Nat, evaluate equalsOne (x ::ᵥ List.Vector.nil) = if x = 1 then 1 else 0) ∧
  (∀ n (q : Program n) v, evaluate (normalize q) v = if evaluate q v = 1 then 1 else 0)

def InternalEqualsOne : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨1, equalsOne⟩ →
  ∀ ctx (x : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (GorbowBooleanTruth.biconditional
      (.equal (GorbowPRDefiningEquations.call tag (x ::ᵥ List.Vector.nil)) (Term.numeral 1))
      (.equal x (Term.numeral 1))))

def InternalNormalizedRange : Prop :=
  ∀ n (q : Program n) m (p : Program m) tag,
  (nodes p)[tag]? = some ⟨n, normalize q⟩ → ∀ ctx (args : List.Vector (Term ctx) n),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (booleanRange (GorbowPRDefiningEquations.call tag args)))

/-- Truth equivalence to ANY actual occurrence of the SAME AST. No assumed
Boolean range or external extensional program equivalence is substituted. -/
def InternalSameASTAcceptance : Prop :=
  ∀ n (q : Program n) m (p : Program m) normalizedTag originalTag,
  (nodes p)[normalizedTag]? = some ⟨n, normalize q⟩ →
  (nodes p)[originalTag]? = some ⟨n, q⟩ → ∀ ctx (args : List.Vector (Term ctx) n),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (GorbowBooleanTruth.biconditional
      (.equal (GorbowPRDefiningEquations.call normalizedTag args) (Term.numeral 1))
      (.equal (GorbowPRDefiningEquations.call originalTag args) (Term.numeral 1))))

/-- A real internal invariant of an actual universal verifier in the published
D. The old c is not silently reused after changing the finite S presentation. -/
def PublishedBooleanVerifier : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : GorbowPublishedDCB.Code),
  GorbowPublishedDCB.Actual pF pR q c →
  ∃ cNew : GorbowPublishedDCB.Code,
    GorbowPublishedDCB.Actual pF pR (normalize q) cNew ∧
    ∀ ctx (args : List.Vector (Term ctx) 5),
    Nonempty (Derivation (GorbowPublishedDCB.D pF pR (normalize q) cNew)
      (booleanRange (GorbowPRDefiningEquations.call
        (GorbowNamedInternalProvability.checkerTag pF) args)))

def Target : Prop := ActualEvaluation ∧ InternalEqualsOne ∧ InternalNormalizedRange ∧
  InternalSameASTAcceptance ∧ PublishedBooleanVerifier

end LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.Targets

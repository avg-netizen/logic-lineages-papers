module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivationDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction
public import LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms

@[expose] public section
/-! The published SENTENCE construction: S is the concrete named arithmetic
base plus Non-triviality, K1-K2 and UKK; rho is its actual named diagonal
reflection sentence; D=S+rho and Pr_D(sigma)=Pr_S(code(rho->sigma)).
No alternative ordinary-program fixed point is silently substituted for rho.
The original source Base/HB adequacy obligations are not asserted here. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector
abbrev Code := Nat.Partrec.Code

def UniversalVerifier (q : Program 5) : Prop := ∀ c fuel n formula certificate,
  evaluate q (GorbowEnumeratedProvability.arguments c fuel n formula certificate) =
    if GorbowEnumeratedProvability.check (c,fuel) n formula certificate then 1 else 0

def augmented (pF : Program 1) (q : Program 5) : Program 1 :=
  GorbowNamedInternalProvability.augment pF q

def axiomsS (pF pR : Program 1) (q : Program 5) : List Sentence :=
  GorbowNamedDefiningTheory.axioms (augmented pF q) pR ++
    [GorbowSortedKnowledgeAxioms.nontriviality, GorbowSortedKnowledgeAxioms.bridge,
      GorbowSortedKnowledgeAxioms.distribution]

def S (pF pR : Program 1) (q : Program 5) : Sentence → Prop :=
  fun sigma => sigma ∈ axiomsS pF pR q

def checkS (pF pR : Program 1) (q : Program 5) (raw : List Nat) : Bool :=
  decide (raw ∈ (axiomsS pF pR q).map GorbowFormulaPrefixCode.encode)

/-- The variable retained outside both existentials is the formula number. -/
def provability (pF : Program 1) (c : Code) : Formula 1 :=
  .ex (.ex (.equal (GorbowPRDefiningEquations.call
    (GorbowNamedInternalProvability.checkerTag pF)
    (Term.numeral (Encodable.encode c) ::ᵥ .var 1 ::ᵥ Term.numeral 0 ::ᵥ .var 2 ::ᵥ
      .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)))

def applyProv {n : Nat} (pF : Program 1) (c : Code) (t : Term n) : Formula n :=
  GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => t) (provability pF c)

/-- Context after both universals is [formula,agent,reflection-code]. -/
def reflectionTemplate (pF : Program 1) (c : Code) : Formula 1 :=
  .all (.imp (.agent (.var 0))
    (.all (.imp (GorbowBooleanTruth.sentenceGuard (.var 0))
      (.imp (applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0 (.var 2) (.var 0)))
        (.knowledge (.var 1) (.var 0))))))

def rho (pF : Program 1) (c : Code) : Sentence :=
  GorbowDiagonalSentence.diagonal (reflectionTemplate pF c)

def D (pF pR : Program 1) (q : Program 5) (c : Code) : Sentence → Prop :=
  GorbowClosedDeduction.extend (S pF pR q) (rho pF c)

def prD (pF : Program 1) (c : Code) (sigma : Sentence) : Sentence :=
  applyProv pF c (GorbowBooleanTruth.binaryCodeTerm 0
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))

def Actual (pF pR : Program 1) (q : Program 5) (c : Code) : Prop :=
  GorbowSelectedDistribution.Calibrated pF pR ∧ UniversalVerifier q ∧
    GorbowEnumeratedProvability.enumeratedTheory c = S pF pR q

end LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB

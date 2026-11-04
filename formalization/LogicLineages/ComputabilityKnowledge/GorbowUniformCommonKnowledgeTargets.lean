module

public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge.Targets
open GorbowSyntax GorbowPRProgram GorbowSortedSyntaxCode

/-- The retained object-language parameter actually occurs. -/
def RetainedParameter : Prop :=
  ∀ tag (A : Selector), (common tag A).uses 0 = true

/-- Exact source syntax, before replacing a closed program call by its numeral. -/
def LiteralBodyRewrite : Prop :=
  ∀ tag (A : Selector) (sigma : Sentence),
    closedInstance tag A sigma =
      GorbowStandardInstances.instantiate (literalBody A sigma) (closedCall tag A sigma)

/-- The body really is the conjunction of the two selected-knowledge clauses. -/
def NumeralBody : Prop :=
  ∀ (A : Selector) (sigma : Sentence) out,
    GorbowStandardInstances.instantiate (literalBody A sigma) (Term.numeral out) =
      .conj (everyone A (formulaCode sigma)) (everyone A out)

/-- A real enriched source construction; no registry/calibration oracle is assumed. -/
def EnrichedParameters : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Nat.Partrec.Code)
      (tag : Nat) (p : Program 2),
    GorbowPublishedDCB.Actual pF pR q c ∧ CodeProgram p ∧ RegistryInstall pF pR q tag p

/-- Literal code equation derived from the finite defining theory inside actual D. -/
def CodeEquation : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Nat.Partrec.Code)
      (tag : Nat) (p : Program 2),
    GorbowPublishedDCB.Actual pF pR q c → CodeProgram p → RegistryInstall pF pR q tag p →
    ∀ (A : Selector) (sigma : Sentence),
      Nonempty (GorbowTheoryProof.Derivation (GorbowPublishedDCB.D pF pR q c)
        (.equal (closedCall tag A sigma) (Term.numeral (formulaCode (closedInstance tag A sigma)))))

/-- Actual Hilbert fixed-point equations for ALL closed sentence parameters. -/
def ClosedFixedPoint : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Nat.Partrec.Code)
      (tag : Nat) (p : Program 2),
    GorbowPublishedDCB.Actual pF pR q c → CodeProgram p → RegistryInstall pF pR q tag p →
      FixedPointFor pF pR q c tag

/-- Existential installation discharges every earlier construction premise. -/
def ConcreteCommonKnowledge : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Nat.Partrec.Code) (tag : Nat),
    GorbowPublishedDCB.Actual pF pR q c ∧ FixedPointFor pF pR q c tag

def Target : Prop := RetainedParameter ∧ LiteralBodyRewrite ∧ NumeralBody ∧
  EnrichedParameters ∧ CodeEquation ∧ ClosedFixedPoint ∧ ConcreteCommonKnowledge
end LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge.Targets

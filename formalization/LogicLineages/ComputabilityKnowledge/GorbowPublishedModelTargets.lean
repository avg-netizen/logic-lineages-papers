module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedModel.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

def GuardCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ I n (t : Term n) env,
  (GorbowBooleanTruth.sentenceGuard t).realize (namedInterpretation pF pR q I) env ↔
    ∃ sigma : Sentence, GorbowSortedSyntaxCode.formulaCode sigma =
      t.realize (namedInterpretation pF pR q I) env

def ImplicationCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ I n (s t : Term n) env (sigma tau : Sentence),
  s.realize (namedInterpretation pF pR q I) env = GorbowSortedSyntaxCode.formulaCode sigma →
  t.realize (namedInterpretation pF pR q I) env = GorbowSortedSyntaxCode.formulaCode tau →
  (GorbowBooleanTruth.binaryCodeTerm 0 s t).realize (namedInterpretation pF pR q I) env =
    GorbowSortedSyntaxCode.formulaCode (.imp sigma tau)

def SProvabilityCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ I n (t : Term n) env,
  (applyProv pF c t).realize (namedInterpretation pF pR q I) env ↔
    ∃ sigma : Sentence, GorbowSortedSyntaxCode.formulaCode sigma =
      t.realize (namedInterpretation pF pR q I) env ∧
      Nonempty (Derivation (S pF pR q) sigma)

def DProvabilityCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ I (sigma : Sentence),
  (prD pF c sigma).realize (namedInterpretation pF pR q I) Fin.elim0 ↔
    Nonempty (Derivation (D pF pR q c) sigma)

/-- Every literal actual D AXIOM holds in this concrete standard-N model.
The reflection sentence is not assumed true or added as a model field. -/
def TheoremSetModel : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ sigma : Sentence, D pF pR q c sigma →
    sigma.realize (theoremModel pF pR q c) Fin.elim0

def Consistency : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ¬ Nonempty (Derivation (D pF pR q c) falseEquality)

def Target : Prop := GuardCalibration ∧ ImplicationCalibration ∧ SProvabilityCalibration ∧
  DProvabilityCalibration ∧ TheoremSetModel ∧ Consistency

end LogicLineages.ComputabilityKnowledge.GorbowPublishedModel.Targets

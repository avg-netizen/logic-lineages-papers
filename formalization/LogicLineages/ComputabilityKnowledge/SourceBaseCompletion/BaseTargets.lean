module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Explicitly expose ALL closed PA(L) instances, including induction with
arbitrary truth/knowledge formulas and retained parameters, in ANY theory. -/
def FullPAAvailability : Prop :=
  ∀ (T : Sentence → Prop) n (w : GorbowPACore.ArithmeticInstance n),
    Nonempty (Derivation T (GorbowStandardInduction.universalClosure
      (GorbowPACore.arithmeticFormula w)))

def ActualSyntaxAdequacy : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    SyntaxAdequate pF pR q

/-- Every intrinsic PA axiom and every extra syntax axiom holds throughout
the SAME actual revision sequence used by the full KT/FS/UBF proof. -/
def BaseRevisionValidity : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ k,
    (∀ n (w : GorbowPACore.ArithmeticInstance n),
      (GorbowStandardInduction.universalClosure (GorbowPACore.arithmeticFormula w)).realize
        (GorbowPublishedRevision.stage pF pR q c k) Fin.elim0) ∧
    (∀ sigma : Sentence, Base pF pR q sigma →
      sigma.realize (GorbowPublishedRevision.stage pF pR q c k) Fin.elim0)

/-- The SAME numeral-code formula used in reflection represents precisely
proofs in D itself, not in KT or an unrelated finite theory. -/
def SelfIndexedCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ (I : Interpretation) (sigma : Sentence),
    ((prD pF c sigma).realize (GorbowPublishedModel.namedInterpretation pF pR q I) Fin.elim0 ↔
      Nonempty (Derivation (D pF pR q c) sigma)) ∧
    (Nonempty (Derivation (D pF pR q c) sigma) →
      Nonempty (Derivation (D pF pR q c) (prD pF c sigma)))

/-- All three selected-agent clauses and BOTH full KT theories, in ONE
actual parameter choice whose entire named Base contract has been proved.
No Base soundness, proof adequacy, consistency or HB premise is supplied. -/
def CompleteSourcePair : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code),
    Actual pF pR q c ∧ SyntaxAdequate pF pR q ∧
    (∀ (A : Selector) (sigma tau : Sentence),
      (Nonempty (Derivation (D pF pR q c) sigma) →
        Nonempty (Derivation (D pF pR q c)
          (everyone A (GorbowSortedSyntaxCode.formulaCode sigma)))) ∧
      Nonempty (Derivation (D pF pR q c)
        (GorbowSelectedDistribution.selectedDistribution A sigma tau)) ∧
      Nonempty (Derivation (D pF pR q c)
        (.imp (prD pF c sigma) (everyone A (GorbowSortedSyntaxCode.formulaCode sigma))))) ∧
    (¬ Nonempty (GorbowPublishedKT.Proof false pF pR q c falseEquality)) ∧
    (¬ Nonempty (GorbowPublishedKT.Proof true pF pR q c falseEquality))

def Target : Prop := FullPAAvailability ∧ ActualSyntaxAdequacy ∧
  BaseRevisionValidity ∧ SelfIndexedCalibration ∧ CompleteSourcePair

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.Targets

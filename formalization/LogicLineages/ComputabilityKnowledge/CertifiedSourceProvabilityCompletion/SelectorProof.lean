module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SelectorTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteIterationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode GorbowFormulaSubstitution

private def selectorBody (A : Selector) : Formula 1 :=
  .imp (.agent (.var 0)) (.imp A.val
    (.knowledge (.var 0) (Term.numeral (formulaCode falseEquality))))

private def veracityMatrix : Formula 2 :=
  .imp (GorbowBooleanTruth.sentenceGuard (.var 0))
    (.imp (.knowledge (.var 1) (.var 0)) (.truth (.var 0)))

private theorem veracityMatrixAt (code : Nat) :
    GorbowStandardInstances.instantiate veracityMatrix (Term.numeral code : Term 1) =
      .imp (GorbowBooleanTruth.sentenceGuard (Term.numeral code))
        (.imp (.knowledge (.var 0) (Term.numeral code)) (.truth (Term.numeral code))) := by
  simp only [veracityMatrix, GorbowStandardInstances.instantiate, substituteFormula,
    GorbowBooleanTruth.sentenceGuard, GorbowSubstitution.substitute,
    GorbowHeaderSubstitutionProof.headers, List.map_cons, List.map_nil,
    GorbowHeaderSubstitutionProof.numerals]
  rfl

/-- Literal source veracity at the contradiction, with its guards discharged
inside actual KT. The agent is a free object variable, not a chosen witness. -/
theorem contradictionVeracity (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) :
    Nonempty (Derivation (n := 1) (GorbowPublishedKT.Axiom false pF pR q c)
      (.imp (.agent (.var 0))
        (.imp (.knowledge (.var 0) (Term.numeral (formulaCode falseEquality)))
          (.equal .zero (.succ .zero))))) := by
  let T := GorbowPublishedKT.Axiom false pF pR q c
  let ag : Formula 1 := .agent (.var 0)
  let kb : Formula 1 := .knowledge (.var 0) (Term.numeral (formulaCode falseEquality))
  let tb : Formula 1 := .truth (Term.numeral (formulaCode falseEquality))
  let b : Formula 1 := .equal .zero (.succ .zero)
  obtain ⟨hv⟩ := openUniversal (T := T) (.imp ag (.all veracityMatrix))
    (.axiom GorbowSortedKnowledgeAxioms.veracity .veracity)
  have hi : Derivation T (.imp (.all veracityMatrix)
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral (formulaCode falseEquality)))
        (.imp kb tb))) := by
    have h := Derivation.logical (A := T)
      (.allInstantiate veracityMatrix (Term.numeral (formulaCode falseEquality) : Term 1))
    rw [GorbowPACore.logicalFormula, veracityMatrixAt] at h
    exact h
  have hvg := Hilbert.compose hi hv
  obtain ⟨hg⟩ := contradictionSentenceGuard pF pR q c hA
  obtain ⟨hg1⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ ⟨hg⟩ 1
  have hg1' : Derivation T
      (GorbowBooleanTruth.sentenceGuard (Term.numeral (formulaCode falseEquality) : Term 1)) := by
    rw [liftedGuard] at hg1
    exact hg1
  obtain ⟨htb⟩ := atomicContradictionTruth pF pR q c hA
  obtain ⟨htb1⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ ⟨htb⟩ 1
  have htb1' : Derivation T (.imp tb b) := by
    change Derivation T (weakenClosed 1
      (.imp (.truth (Term.numeral (formulaCode falseEquality))) falseEquality)) at htb1
    rw [liftedTruthImplication] at htb1
    exact htb1
  have hb : Hilbert.Local T 1 [kb, ag] b :=
    .mp (.base htb1')
      (.mp (.mp (.mp (.base hvg)
        (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) (.base hg1'))
        (.hypothesis List.mem_cons_self))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hb))⟩

private theorem selectedNonemptyContradiction (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (A : Selector) (B : Sentence → Prop)
    (hTB : ∀ s, GorbowPublishedKT.Axiom false pF pR q c s → B s)
    (hE : B (everyone A (formulaCode falseEquality)))
    (hN : B (selectedNonempty A)) : Nonempty (Derivation B falseEquality) := by
  let ag : Formula 1 := .agent (.var 0)
  let selected : Formula 1 := .conj ag A.val
  let b : Formula 1 := .equal .zero (.succ .zero)
  obtain ⟨he⟩ := openUniversal (T := B) (selectorBody A) (.axiom _ hE)
  obtain ⟨hv⟩ := contradictionVeracity pF pR q c hA
  obtain ⟨hvB⟩ := GorbowTheoryProofProof.monotonicity _ B hTB 1 _ ⟨hv⟩
  have hs : Hilbert.Local B 1 [selected] selected := .hypothesis List.mem_cons_self
  have ha : Hilbert.Local B 1 [selected] ag := .mp (.base (.logical (.andLeft _ _))) hs
  have hA' : Hilbert.Local B 1 [selected] A.val := .mp (.base (.logical (.andRight _ _))) hs
  have hb : Hilbert.Local B 1 [selected] b :=
    .mp (.mp (.base hvB) ha) (.mp (.mp (.base he) ha) hA')
  have hsb : Derivation B (.imp selected b) := Hilbert.Local.finish (Hilbert.Local.discharge hb)
  obtain ⟨hnb⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals B 0 1 (by decide)
  obtain ⟨hnb1⟩ := GorbowDerivationSubstitution.Proof.closedLifting B _ ⟨hnb⟩ 1
  have hnotselected : Derivation B (.neg selected) := Hilbert.modusTollens hsb hnb1
  have hforall : Derivation B (.all (.neg selected)) := .generalize hnotselected
  have hn : Derivation B (selectedNonempty A) := by
    have h := Derivation.axiom (A := B) (n := 0) _ hN
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hnotforall : Derivation B (.neg (.all (.neg selected))) :=
    .mp (.logical (.existsDualForward selected)) hn
  exact ⟨Hilbert.explosion falseEquality hforall hnotforall⟩

private theorem nonemptyToTheta (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (A : Selector) :
    Nonempty (Derivation (GorbowPublishedKT.Axiom false pF pR q c)
      (.imp (selectedNonempty A) (selectorTheta A))) := by
  let T := GorbowPublishedKT.Axiom false pF pR q c
  let N := selectedNonempty A
  let E := everyone A (formulaCode falseEquality)
  let BN := GorbowClosedDeduction.extend T N
  let B := GorbowClosedDeduction.extend BN E
  obtain ⟨hb⟩ := selectedNonemptyContradiction pF pR q c hA A B
    (fun _ h => Or.inl (Or.inl h)) (Or.inr rfl) (Or.inl (Or.inr rfl))
  obtain ⟨htheta⟩ := GorbowClosedDeductionProof.deduction BN E 0 falseEquality hb
  rw [GorbowClosedDeductionProof.closedSyntax.1] at htheta
  obtain ⟨h⟩ := GorbowClosedDeductionProof.deduction T N 0 (selectorTheta A) htheta
  exact ⟨by simpa only [GorbowClosedDeductionProof.closedSyntax.1] using h⟩

private theorem thetaToNonempty (pF pR : Program 1) (q : Program 5) (c : Code)
    (A : Selector) :
    Nonempty (Derivation (GorbowPublishedKT.Axiom false pF pR q c)
      (.imp (selectorTheta A) (selectedNonempty A))) := by
  let T := GorbowPublishedKT.Axiom false pF pR q c
  let N := selectedNonempty A
  let E := everyone A (formulaCode falseEquality)
  let B := GorbowClosedDeduction.extend T (selectorTheta A)
  let C := GorbowClosedDeduction.extend B (.neg N)
  let ag : Formula 1 := .agent (.var 0)
  let selected : Formula 1 := .conj ag A.val
  let kb : Formula 1 := .knowledge (.var 0) (Term.numeral (formulaCode falseEquality))
  let allNot := Formula.all (.neg selected)
  have hnN : Derivation C (.neg N) := by
    have h := Derivation.axiom (A := C) (n := 0) (.neg N) (Or.inr rfl)
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hd : Derivation C (.imp (.neg allNot) N) := .logical (.existsDualBackward selected)
  have hnnall : Derivation C (.neg (.neg allNot)) := Hilbert.modusTollens hd hnN
  have hall : Derivation C allNot := .mp (Hilbert.doubleNegation allNot) hnnall
  obtain ⟨hall1⟩ := GorbowDerivationSubstitution.Proof.closedLifting C allNot ⟨hall⟩ 1
  obtain ⟨hnotselected⟩ := openUniversal (T := C) (.neg selected) hall1
  have ha : Hilbert.Local C 1 [A.val, ag] ag :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hA' : Hilbert.Local C 1 [A.val, ag] A.val := .hypothesis List.mem_cons_self
  have hs : Hilbert.Local C 1 [A.val, ag] selected :=
    .mp (.mp (.base (.logical (.andIntro _ _))) ha) hA'
  have hk : Hilbert.Local C 1 [A.val, ag] kb :=
    Hilbert.Local.explosion kb hs (.base hnotselected)
  have heOpen : Derivation C (.imp ag (.imp A.val kb)) :=
    Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hk))
  have he : Derivation C E := .generalize heOpen
  have ht : Derivation C (selectorTheta A) := by
    have h := Derivation.axiom (A := C) (n := 0) (selectorTheta A) (Or.inl (Or.inr rfl))
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hb : Derivation C falseEquality := .mp ht he
  obtain ⟨hnb⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals C 0 1 (by decide)
  have hN : Derivation C N := Hilbert.explosion N hb hnb
  obtain ⟨hN'⟩ := GorbowClassicalDerivation.Proof.closedReductio B N hN
  obtain ⟨h⟩ := GorbowClosedDeductionProof.deduction T (selectorTheta A) 0 N hN'
  exact ⟨by simpa only [GorbowClosedDeductionProof.closedSyntax.1] using h⟩

theorem firstSelector : SelectorTargets.FirstSelector := by
  intro pF pR q c hA A
  obtain ⟨hf⟩ := thetaToNonempty pF pR q c A
  obtain ⟨hb⟩ := nonemptyToTheta pF pR q c hA A
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hf) hb⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof

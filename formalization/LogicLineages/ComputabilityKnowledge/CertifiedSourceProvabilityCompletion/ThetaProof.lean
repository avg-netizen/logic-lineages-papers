module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.AtomicTruthProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowFormulaSubstitution GorbowSortedSyntaxCode

private theorem substNum {m n : Nat} (sigma : Fin m → Term n) (k : Nat) :
    GorbowSubstitution.substitute sigma (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n sigma k

private theorem substHeader {m n : Nat} (sigma : Fin m → Term n) (arity tag : Nat)
    (args : List (Term m)) :
    GorbowSubstitution.substitute sigma (GorbowRegistryTuple.headerTerm arity tag args) =
      GorbowRegistryTuple.headerTerm arity tag (args.map (GorbowSubstitution.substitute sigma)) :=
  GorbowHeaderSubstitutionProof.headers m n sigma arity tag args

private theorem liftVariables (n : Nat) :
    liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaVariables {n : Nat} (phi : Formula n) :
    substituteFormula Term.var phi = phi := by
  induction phi with
  | equal t u | knowledge t u =>
      simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
      simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | neg phi ih => simp only [substituteFormula, ih]
  | imp phi psi hp hq | conj phi psi hp hq | disj phi psi hp hq =>
      simp only [substituteFormula, hp, hq]
  | all phi ih | ex phi ih => simp only [substituteFormula, liftVariables, ih]

theorem openUniversal {T : Sentence → Prop} (B : Formula 1)
    (h : Derivation T (weakenClosed 1 (.all B))) : Nonempty (Derivation T B) := by
  have h' : Derivation T
      (.all (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B)) := h
  have r := Derivation.mp (Derivation.logical (A := T)
    (.allInstantiate (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B)
      (Term.var 0))) h'
  have hv : (fun i : Fin 1 => GorbowSubstitution.substitute
      (Fin.cases (Term.var 0) Term.var : Fin 2 → Term 1)
      (liftSubstitute (Fin.elim0 : Fin 0 → Term 1) i)) = Term.var := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  have he : GorbowStandardInstances.instantiate
      (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B) (Term.var 0) = B := by
    unfold GorbowStandardInstances.instantiate
    rw [GorbowFormulaCompositionProof.composition, hv, formulaVariables]
  exact ⟨he ▸ r⟩

private def topBody (code : Nat) : Formula 1 :=
  .imp (.agent (.var 0)) (.imp (.equal (.var 0) (.var 0))
    (.knowledge (.var 0) (Term.numeral code)))

private def veracityInner : Formula 2 :=
  .imp (GorbowBooleanTruth.sentenceGuard (.var 0))
    (.imp (.knowledge (.var 1) (.var 0)) (.truth (.var 0)))

private def veracityBody : Formula 1 := .imp (.agent (.var 0)) (.all veracityInner)

private theorem veracityAt (code : Nat) :
    GorbowStandardInstances.instantiate veracityInner (Term.numeral code : Term 1) =
      .imp (GorbowBooleanTruth.sentenceGuard (Term.numeral code))
        (.imp (.knowledge (.var 0) (Term.numeral code)) (.truth (Term.numeral code))) := by
  simp only [veracityInner, GorbowStandardInstances.instantiate, substituteFormula,
    GorbowBooleanTruth.sentenceGuard, GorbowSubstitution.substitute]
  rfl

theorem liftedGuard (code : Nat) :
    weakenClosed 1 (GorbowBooleanTruth.sentenceGuard (Term.numeral code : Term 0)) =
      GorbowBooleanTruth.sentenceGuard (Term.numeral code : Term 1) := by
  simp only [weakenClosed, GorbowBooleanTruth.sentenceGuard, substituteFormula,
    substHeader, List.map_cons, List.map_nil, substNum]

/-- Keep the formula number symbolic while transporting closed syntax;
normalizing a concrete Gödel numeral is unnecessary. -/
theorem liftedTruthImplication (code : Nat) :
    weakenClosed 1 (.imp (.truth (Term.numeral code)) falseEquality) =
      (.imp (.truth (Term.numeral code : Term 1)) (.equal .zero (.succ .zero))) := by
  simp only [weakenClosed, substituteFormula, substNum, falseEquality,
    GorbowSubstitution.substitute]

theorem directTheta : Targets.DirectTheta := by
  intro pF pR q c hA
  let T := GorbowPublishedKT.Axiom false pF pR q c
  let eb := everyone topSelector (formulaCode falseEquality)
  let B := GorbowClosedDeduction.extend T eb
  let ag : Formula 1 := .agent (.var 0)
  let kb : Formula 1 := .knowledge (.var 0) (Term.numeral (formulaCode falseEquality))
  let tb : Formula 1 := .truth (Term.numeral (formulaCode falseEquality))
  let b : Formula 1 := .equal .zero (.succ .zero)
  obtain ⟨he⟩ := openUniversal (T := B) (topBody (formulaCode falseEquality))
    (.axiom eb (Or.inr rfl))
  have hr : Derivation B (.equal (.var 0 : Term 1) (.var 0)) := .logical (.reflexive _)
  have hak : Derivation B (.imp ag kb) := Hilbert.mpUnder he (Hilbert.lift ag hr)
  obtain ⟨hv⟩ := openUniversal (T := B) veracityBody
    (.axiom GorbowSortedKnowledgeAxioms.veracity (Or.inl .veracity))
  have hi : Derivation B (.imp (.all veracityInner)
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral (formulaCode falseEquality)))
        (.imp kb tb))) := by
    have h := Derivation.logical (A := B)
      (.allInstantiate veracityInner (Term.numeral (formulaCode falseEquality) : Term 1))
    rw [GorbowPACore.logicalFormula, veracityAt] at h
    exact h
  have hvg := Hilbert.compose hi hv
  obtain ⟨hg⟩ := contradictionSentenceGuard pF pR q c hA
  obtain ⟨hgB⟩ := GorbowTheoryProofProof.monotonicity T B (fun _ h => Or.inl h) 0 _ ⟨hg⟩
  obtain ⟨hg1⟩ := GorbowDerivationSubstitution.Proof.closedLifting B _ ⟨hgB⟩ 1
  rw [liftedGuard] at hg1
  have hakt : Derivation B (.imp ag (.imp kb tb)) :=
    Hilbert.mpUnder hvg (Hilbert.lift ag hg1)
  have hat : Derivation B (.imp ag tb) := Hilbert.mpUnder hakt hak
  obtain ⟨htb⟩ := atomicContradictionTruth pF pR q c hA
  obtain ⟨htbB⟩ := GorbowTheoryProofProof.monotonicity T B (fun _ h => Or.inl h) 0 _ ⟨htb⟩
  obtain ⟨htb1⟩ := GorbowDerivationSubstitution.Proof.closedLifting B _ ⟨htbB⟩ 1
  have htb1' : Derivation B (.imp tb b) := by
    change Derivation B (weakenClosed 1
      (.imp (.truth (Term.numeral (formulaCode falseEquality))) falseEquality)) at htb1
    rw [liftedTruthImplication] at htb1
    exact htb1
  have hab : Derivation B (.imp ag b) := Hilbert.compose htb1' hat
  obtain ⟨hnb⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals B 0 1 (by decide)
  obtain ⟨hnb1⟩ := GorbowDerivationSubstitution.Proof.closedLifting B _ ⟨hnb⟩ 1
  have hnb1' : Derivation B (.neg b) := hnb1
  have hna : Derivation B (.neg ag) := Hilbert.modusTollens hab hnb1'
  have hforall : Derivation B (.all (.neg ag)) := .generalize hna
  have hnmem : T GorbowSortedKnowledgeAxioms.nontriviality :=
    .d _ (Or.inl (List.mem_append.mpr (Or.inr (by simp))))
  have hn : Derivation B GorbowSortedKnowledgeAxioms.nontriviality := by
    have h := Derivation.axiom (A := B) (n := 0)
      GorbowSortedKnowledgeAxioms.nontriviality (Or.inl hnmem)
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hnotforall : Derivation B (.neg (.all (.neg ag))) :=
    .mp (.logical (.existsDualForward ag)) hn
  have hcontr : Derivation B falseEquality := Hilbert.explosion falseEquality hforall hnotforall
  obtain ⟨hresult⟩ := GorbowClosedDeductionProof.deduction T eb 0 falseEquality hcontr
  rw [GorbowClosedDeductionProof.closedSyntax.1] at hresult
  exact ⟨.ordinary hresult⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof

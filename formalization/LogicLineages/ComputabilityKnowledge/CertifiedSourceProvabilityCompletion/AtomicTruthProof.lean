module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Targets
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode GorbowNamedNumeralCertificates GorbowRegistryTuple List.Vector

theorem baseIntoKT (pF pR : Program 1) (q : Program 5) (c : Code)
    (sigma : Sentence) (h : SourceBaseCompletion.Base pF pR q sigma) :
    GorbowPublishedKT.Axiom false pF pR q c sigma :=
  .d sigma (Or.inl (List.mem_append.mpr (Or.inl h)))

theorem contradictionInstanceCode (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) :
    Nonempty (Derivation (GorbowPublishedKT.Axiom false pF pR q c)
      (.equal (GorbowAtomicTruth.instanceCodeTerm falseEquality
        (Fin.elim0 : Fin 0 → Fin 0)) (Term.numeral (formulaCode falseEquality)))) := by
  let v : List.Vector Nat 3 := 0 ::ᵥ formulaCode falseEquality ::ᵥ 0 ::ᵥ nil
  have hm : ((3, 1) : Nat × Nat) ∈ GorbowSourceRegistryPadding.functionNames := by
    simp [GorbowSourceRegistryPadding.functionNames]
  have hs : GorbowAtomicRegistry.tupleSubstitute 0 (formulaCode falseEquality) 0 =
      some (formulaCode falseEquality) := by
    apply (GorbowAtomicRegistryProof.tupleExact 0 (formulaCode falseEquality) 0
      (formulaCode falseEquality)).mpr
    refine ⟨[], rfl, ?_⟩
    simpa only [List.ofFn_zero, falseEquality,
      GorbowFormulaSubstitution.substituteFormula, GorbowSubstitution.substitute] using
      GorbowSortedSimultaneousCodeProof.actualCalibration 0 falseEquality
        (Fin.elim0 : Fin 0 → Term 0)
  have hv : GorbowSourceRegistryPadding.sourceFunction (inputCode (3, 1) v) =
      formulaCode falseEquality := by
    change GorbowDiagonalRegistry.functionProgram
      (header 3 1 [0, formulaCode falseEquality, 0]) = formulaCode falseEquality
    rw [(GorbowDiagonalRegistryProof.atomicDispatch 0 (formulaCode falseEquality) 0).2, hs]
    rfl
  have hS := SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA
  obtain ⟨h⟩ := ((hS.1 (3, 1) hm v (formulaCode falseEquality)).1).mpr hv
  have he : GorbowAtomicTruth.instanceCodeTerm falseEquality
      (Fin.elim0 : Fin 0 → Fin 0) =
      .universalFunction (inputHeader (3, 1) v) := by
    rfl
  rw [he]
  exact GorbowTheoryProofProof.monotonicity (SourceBaseCompletion.Base pF pR q)
    (GorbowPublishedKT.Axiom false pF pR q c) (baseIntoKT pF pR q c) 0 _ ⟨h⟩

theorem atomicContradictionTruth : Targets.AtomicContradictionTruth := by
  intro pF pR q c hA
  let T := GorbowPublishedKT.Axiom false pF pR q c
  let codeTerm := GorbowAtomicTruth.instanceCodeTerm falseEquality
    (Fin.elim0 : Fin 0 → Fin 0)
  have hcovers : GorbowNameDictionary.Covers falseEquality
      (Fin.elim0 : Fin 0 → Fin 0) := by
    simp [GorbowNameDictionary.Covers, GorbowFreeSupport.formulaSupport,
      GorbowFreeSupport.termSupport, falseEquality]
  have ha : T (GorbowAtomicTruth.atomicAxiom falseEquality
      (Fin.elim0 : Fin 0 → Fin 0)) :=
    .atomic falseEquality Fin.elim0 trivial (fun i => Fin.elim0 i) hcovers
  have hd : Derivation T (GorbowBooleanTruth.biconditional (.truth codeTerm) falseEquality) := by
    have h := Derivation.axiom (n := 0) _ ha
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hf : Derivation T (.imp (.truth codeTerm) falseEquality) :=
    .mp (.logical (.andLeft _ _)) hd
  obtain ⟨he⟩ := contradictionInstanceCode pF pR q c hA
  let phi : Formula 1 := .imp (.truth (.var 0)) (.equal .zero (.succ .zero))
  obtain ⟨hr⟩ := GorbowTheoryEqualityProof.formulaImplication T phi codeTerm
    (Term.numeral (formulaCode falseEquality)) he
  exact ⟨Derivation.mp hr hf⟩

theorem contradictionSentenceGuard (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) :
    Nonempty (Derivation (n := 0) (GorbowPublishedKT.Axiom false pF pR q c)
      (GorbowBooleanTruth.sentenceGuard (Term.numeral (formulaCode falseEquality)))) := by
  have hm : ((1, 0) : Nat × Nat) ∈ GorbowSourceRegistryPadding.relationNames := by
    simp [GorbowSourceRegistryPadding.relationNames]
  have hv : GorbowSortedRegistry.relationProgram (header 1 0 [formulaCode falseEquality]) =
      true :=
    (GorbowSortedRegistryProof.relationDispatch (formulaCode falseEquality) 0).1.trans
      ((GorbowSortedBooleanCodeProof.exactDomains.1 _).mpr ⟨falseEquality, rfl⟩)
  have hS := SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA
  obtain ⟨h⟩ := ((hS.2.1 (1, 0) hm (formulaCode falseEquality ::ᵥ nil)).1).mpr hv
  exact GorbowTheoryProofProof.monotonicity (SourceBaseCompletion.Base pF pR q)
    (GorbowPublishedKT.Axiom false pF pR q c) (baseIntoKT pF pR q c) 0 _ ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof

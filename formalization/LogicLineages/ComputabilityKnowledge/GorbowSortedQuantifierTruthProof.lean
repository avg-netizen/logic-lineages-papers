module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedQuantifierTruth
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruthProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision GorbowFreeSupport GorbowNamedBinding
open GorbowFormulaComposition GorbowStandardInstances GorbowSortedQuantifierTruth GorbowRegistryTuple GorbowBooleanTruth

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ=header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as
private theorem variableRaw {n : Nat} (t : Term n) P ρ :
    (variableGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
      GorbowSortedSyntaxCode.isVariableCode (t.realize (interpretation GorbowSortedRegistry.ground P) ρ)=true := by
  change GorbowSortedRegistry.relationProgram ((headerTerm 1 3 [t]).realize _ ρ)=true ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(GorbowSortedRegistryProof.relationDispatch (t.realize (interpretation GorbowSortedRegistry.ground P) ρ) 0).2.2.2.1]
private theorem fullRaw {n : Nat} (t : Term n) P ρ :
    (fullTermGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
      GorbowSortedBooleanCode.fullTermCode (t.realize (interpretation GorbowSortedRegistry.ground P) ρ)=true := by
  change GorbowSortedRegistry.relationProgram ((headerTerm 1 1 [t]).realize _ ρ)=true ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(GorbowSortedRegistryProof.relationDispatch (t.realize (interpretation GorbowSortedRegistry.ground P) ρ) 0).2.1]
private theorem arithmeticRaw {n : Nat} (t : Term n) P ρ :
    (arithmeticTermGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
      GorbowSortedBooleanCode.arithmeticTermCode (t.realize (interpretation GorbowSortedRegistry.ground P) ρ)=true := by
  change GorbowSortedRegistry.relationProgram ((headerTerm 1 2 [t]).realize _ ρ)=true ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(GorbowSortedRegistryProof.relationDispatch (t.realize (interpretation GorbowSortedRegistry.ground P) ρ) 0).2.2.1]
private theorem namedRaw {n : Nat} (v f : Term n) P ρ :
    (namedGuard v f).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
      GorbowSortedNamedCode.namedFormula (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ)=true := by
  change GorbowSortedRegistry.relationProgram ((headerTerm 2 0 [v,f]).realize _ ρ)=true ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(GorbowSortedRegistryProof.relationDispatch (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ)).2.2.2.2]
private theorem allRaw {n : Nat} (v f : Term n) P ρ :
    (allCodeTerm v f).realize (interpretation GorbowSortedRegistry.ground P) ρ =
      (GorbowSortedNamedCode.allNumber (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ)).getD 0 := by
  change GorbowSortedRegistry.functionProgram ((headerTerm 2 3 [v,f]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (GorbowSortedRegistryProof.functionDispatch (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ) 0).2.2.2.2.1
private theorem exRaw {n : Nat} (v f : Term n) P ρ :
    (exCodeTerm v f).realize (interpretation GorbowSortedRegistry.ground P) ρ =
      (GorbowSortedNamedCode.exNumber (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ)).getD 0 := by
  change GorbowSortedRegistry.functionProgram ((headerTerm 2 4 [v,f]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (GorbowSortedRegistryProof.functionDispatch (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ) 0).2.2.2.2.2.1
private theorem instanceRaw {n : Nat} (v f t : Term n) P ρ :
    (instanceCodeTerm v f t).realize (interpretation GorbowSortedRegistry.ground P) ρ =
      (GorbowSortedNamedCode.instanceNumber (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ) (t.realize (interpretation GorbowSortedRegistry.ground P) ρ)).getD 0 := by
  change GorbowSortedRegistry.functionProgram ((headerTerm 3 0 [v,f,t]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (GorbowSortedRegistryProof.functionDispatch (v.realize (interpretation GorbowSortedRegistry.ground P) ρ) (f.realize (interpretation GorbowSortedRegistry.ground P) ρ) (t.realize (interpretation GorbowSortedRegistry.ground P) ρ)).2.2.2.2.2.2

theorem guardDomains : Comparators.GorbowSortedQuantifierTruth.GuardDomains := by
  intro n t P ρ
  exact ⟨(variableRaw t P ρ).trans (GorbowSortedSyntaxCodeProof.actualCalibration.2.2.2.2 _),
    (fullRaw t P ρ).trans (GorbowSortedBooleanCodeProof.exactDomains.2.1 _),
    (arithmeticRaw t P ρ).trans (GorbowSortedBooleanCodeProof.exactDomains.2.2 _)⟩
theorem namedDomain : Comparators.GorbowSortedQuantifierTruth.NamedDomain := by
  intro k v f P ρ
  exact (namedRaw v f P ρ).trans (GorbowSortedNamedCodeProof.exactNamedDomain _ _)
theorem bindingFunctions : Comparators.GorbowSortedQuantifierTruth.BindingFunctions := by
  intro n φ i hs k v f P ρ hv hf
  obtain ⟨ha,hx,hi⟩ := GorbowSortedNamedCodeProof.originalCalibration n φ i hs
  constructor
  · rw [allRaw,hv,hf,ha]; rfl
  · rw [exRaw,hv,hf,hx]; rfl
theorem instanceFunction : Comparators.GorbowSortedQuantifierTruth.InstanceFunction := by
  intro n φ i hs s k v f t P ρ hv hf ht
  have hi := (GorbowSortedNamedCodeProof.originalCalibration n φ i hs).2.2 s
  rw [instanceRaw,hv,hf,ht,hi]
  rfl

private theorem truthAt (g : Ground) (initial : Extension) (k : Nat) (σ : Sentence) :
    (truthSentence σ).realize (stage g initial k) Fin.elim0 ↔ extensions g initial k (formulaCode σ) := by
  simp [truthSentence,formulaQuote,Formula.realize,numeral_realize,stage,interpretation,GorbowRevisionSemantics.interpretation]
private theorem knowledgeAt (g : Ground) (initial : Extension) (k a : Nat) (σ : Sentence) :
    (knowledgeSentence a σ).realize (stage g initial k) Fin.elim0 ↔ a=0 ∧ extensions g initial k (formulaCode σ) := by
  simp [knowledgeSentence,formulaQuote,Formula.realize,numeral_realize,stage,interpretation,GorbowRevisionSemantics.interpretation]

private theorem numericClauses (initial : Extension) (k varCode code : Nat)
    (hn : GorbowSortedNamedCode.namedFormula varCode code=true) :
    (extensions GorbowSortedRegistry.ground initial (k+1) ((GorbowSortedNamedCode.allNumber varCode code).getD 0) ↔
      ∀ t, GorbowSortedBooleanCode.fullTermCode t=true → extensions GorbowSortedRegistry.ground initial (k+1) ((GorbowSortedNamedCode.instanceNumber varCode code t).getD 0)) ∧
    (extensions GorbowSortedRegistry.ground initial (k+1) ((GorbowSortedNamedCode.exNumber varCode code).getD 0) ↔
      ∃ t, GorbowSortedBooleanCode.fullTermCode t=true ∧ extensions GorbowSortedRegistry.ground initial (k+1) ((GorbowSortedNamedCode.instanceNumber varCode code t).getD 0)) ∧
    (∀ a, a=0 → (∀ t, GorbowSortedBooleanCode.arithmeticTermCode t=true →
      a=0 ∧ extensions GorbowSortedRegistry.ground initial (k+1) ((GorbowSortedNamedCode.instanceNumber varCode code t).getD 0)) →
      a=0 ∧ extensions GorbowSortedRegistry.ground initial (k+1) ((GorbowSortedNamedCode.allNumber varCode code).getD 0)) := by
  obtain ⟨n,φ,v,rfl,rfl,hs⟩ := (GorbowSortedNamedCodeProof.exactNamedDomain varCode code).mp hn
  obtain ⟨σ,τ,hσ,hτ,hq⟩ := GorbowSortedRevisionCompositionProof.namedQuantifiers n v φ hs
  obtain ⟨ha,hx,hi⟩ := GorbowSortedNamedCodeProof.originalCalibration n φ v hs
  have hca : (GorbowSortedNamedCode.allNumber (variableNumber v.val) (formulaCode φ)).getD 0=formulaCode σ := by rw [ha]; exact hσ.symm
  have hcx : (GorbowSortedNamedCode.exNumber (variableNumber v.val) (formulaCode φ)).getD 0=formulaCode τ := by rw [hx]; exact hτ.symm
  have hci (t : Term 0) : (GorbowSortedNamedCode.instanceNumber (variableNumber v.val) (formulaCode φ) (termCode t)).getD 0=formulaCode (namedClosedInstance v φ t) := by rw [hi t]; rfl
  have hqa := (hq GorbowSortedRegistry.ground initial k).1
  have hqx := (hq GorbowSortedRegistry.ground initial k).2.1
  simp only [truthAt] at hqa hqx
  constructor
  · rw [hca,hqa]
    constructor
    · intro h code hc
      obtain ⟨t,rfl⟩ := (GorbowSortedBooleanCodeProof.exactDomains.2.1 code).mp hc
      rw [hci]
      exact h t
    · intro h t
      have ht := h (termCode t) ((GorbowSortedBooleanCodeProof.exactDomains.2.1 _).mpr ⟨t,rfl⟩)
      simpa only [hci] using ht
  constructor
  · rw [hcx,hqx]
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨termCode t,(GorbowSortedBooleanCodeProof.exactDomains.2.1 _).mpr ⟨t,rfl⟩,by simpa only [hci] using ht⟩
    · rintro ⟨code,hc,ht⟩
      obtain ⟨t,rfl⟩ := (GorbowSortedBooleanCodeProof.exactDomains.2.1 code).mp hc
      exact ⟨t,by simpa only [hci] using ht⟩
  · intro a ha0 h
    have htyped : ∀ t : Term 0, ArithmeticTerm t →
        (knowledgeSentence a (namedClosedInstance v φ t)).realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0 := by
      intro t ht
      apply (knowledgeAt _ _ _ _ _).mpr
      have hh := h (termCode t) ((GorbowSortedBooleanCodeProof.exactDomains.2.2 _).mpr ⟨t,rfl,ht⟩)
      simpa only [hci] using hh
    have hout := (hq GorbowSortedRegistry.ground initial k).2.2 a ha0 htyped
    rw [hca]
    exact (knowledgeAt _ _ _ _ _).mp hout

attribute [local irreducible] headerTerm pairTerm tupleTerm

private theorem biconditionalAt {n : Nat} (φ ψ : Formula n) I ρ :
    (biconditional φ ψ).realize I ρ ↔ (φ.realize I ρ ↔ ψ.realize I ρ) := by
  simp only [biconditional,Formula.realize,iff_def]
private theorem truthTermAt {n : Nat} (t : Term n) P ρ :
    (Formula.truth t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔ P (t.realize (interpretation GorbowSortedRegistry.ground P) ρ) := Iff.rfl
private theorem knowledgeTermAt {n : Nat} (a t : Term n) P ρ :
    (Formula.knowledge a t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
      a.realize (interpretation GorbowSortedRegistry.ground P) ρ=0 ∧ P (t.realize (interpretation GorbowSortedRegistry.ground P) ρ) := Iff.rfl

private theorem forallRealization (P : Extension) :
    forallAxiom.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0 ↔
      ∀ v f, (isVariableCode v=true ∧ GorbowSortedNamedCode.namedFormula v f=true) →
        (P ((GorbowSortedNamedCode.allNumber v f).getD 0) ↔ ∀ t, GorbowSortedBooleanCode.fullTermCode t=true → P ((GorbowSortedNamedCode.instanceNumber v f t).getD 0)) := by
  apply forall_congr'
  intro v
  apply forall_congr'
  intro f
  apply imp_congr
  · apply and_congr
    · exact variableRaw (.var 1) P (Fin.cases f (Fin.cases v Fin.elim0))
    · exact namedRaw (.var 1) (.var 0) P (Fin.cases f (Fin.cases v Fin.elim0))
  · rw [biconditionalAt]
    apply iff_congr
    · rw [truthTermAt,allRaw]
      rfl
    · apply forall_congr'
      intro t
      apply imp_congr
      · exact fullRaw (.var 0) P (Fin.cases t (Fin.cases f (Fin.cases v Fin.elim0)))
      · rw [truthTermAt,instanceRaw]
        rfl

private theorem existsRealization (P : Extension) :
    existsAxiom.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0 ↔
      ∀ v f, (isVariableCode v=true ∧ GorbowSortedNamedCode.namedFormula v f=true) →
        (P ((GorbowSortedNamedCode.exNumber v f).getD 0) ↔ ∃ t, GorbowSortedBooleanCode.fullTermCode t=true ∧ P ((GorbowSortedNamedCode.instanceNumber v f t).getD 0)) := by
  apply forall_congr'
  intro v
  apply forall_congr'
  intro f
  apply imp_congr
  · apply and_congr
    · exact variableRaw (.var 1) P (Fin.cases f (Fin.cases v Fin.elim0))
    · exact namedRaw (.var 1) (.var 0) P (Fin.cases f (Fin.cases v Fin.elim0))
  · rw [biconditionalAt]
    apply iff_congr
    · rw [truthTermAt,exRaw]
      rfl
    · apply exists_congr
      intro t
      apply and_congr
      · exact fullRaw (.var 0) P (Fin.cases t (Fin.cases f (Fin.cases v Fin.elim0)))
      · rw [truthTermAt,instanceRaw]
        rfl

private theorem barcanRealization (P : Extension) :
    barcanAxiom.realize (interpretation GorbowSortedRegistry.ground P) Fin.elim0 ↔
      ∀ a v f, (a=0 ∧ isVariableCode v=true ∧ GorbowSortedNamedCode.namedFormula v f=true) →
        (∀ t, GorbowSortedBooleanCode.arithmeticTermCode t=true → a=0 ∧ P ((GorbowSortedNamedCode.instanceNumber v f t).getD 0)) →
        a=0 ∧ P ((GorbowSortedNamedCode.allNumber v f).getD 0) := by
  apply forall_congr'
  intro a
  apply forall_congr'
  intro v
  apply forall_congr'
  intro f
  apply imp_congr
  · apply and_congr Iff.rfl
    apply and_congr
    · exact variableRaw (.var 1) P (Fin.cases f (Fin.cases v (Fin.cases a Fin.elim0)))
    · exact namedRaw (.var 1) (.var 0) P (Fin.cases f (Fin.cases v (Fin.cases a Fin.elim0)))
  · apply imp_congr
    · apply forall_congr'
      intro t
      apply imp_congr
      · exact arithmeticRaw (.var 0) P (Fin.cases t (Fin.cases f (Fin.cases v (Fin.cases a Fin.elim0))))
      · rw [knowledgeTermAt,instanceRaw]
        rfl
    · rw [knowledgeTermAt,allRaw]
      rfl

theorem positiveAxioms : Comparators.GorbowSortedQuantifierTruth.PositiveAxioms := by
  intro initial k
  refine ⟨(forallRealization _).mpr ?_,(existsRealization _).mpr ?_,(barcanRealization _).mpr ?_⟩
  · intro v f h
    exact (numericClauses initial k v f h.2).1
  · intro v f h
    exact (numericClauses initial k v f h.2).2.1
  · intro a v f h
    exact (numericClauses initial k v f h.2.2).2.2 a h.1

theorem gorbowSortedQuantifierTruth : Comparators.GorbowSortedQuantifierTruth.Target :=
  ⟨guardDomains,namedDomain,bindingFunctions,instanceFunction,positiveAxioms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruthProof

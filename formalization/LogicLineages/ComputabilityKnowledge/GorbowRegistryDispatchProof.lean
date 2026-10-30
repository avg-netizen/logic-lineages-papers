module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryDispatch
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionCompositionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatchProof
open GorbowSortedRevision GorbowRegistryDispatch

namespace BooleanSpec
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision GorbowBooleanTruth

def GuardCalibration (g0 : Ground) : Prop := ∀ n (t : Term n) P ρ,
  (sentenceGuard t).realize (interpretation g0 P) ρ ↔
    ∃ σ : Sentence,t.realize (interpretation g0 P) ρ=formulaCode σ

def FunctionCalibration (g0 : Ground) : Prop := ∀ n (s t : Term n) P ρ (σ τ : Sentence),
  s.realize (interpretation g0 P) ρ=formulaCode σ →
  t.realize (interpretation g0 P) ρ=formulaCode τ →
  (negCodeTerm s).realize (interpretation g0 P) ρ=formulaCode (.neg σ) ∧
  (binaryCodeTerm 0 s t).realize (interpretation g0 P) ρ=formulaCode (.imp σ τ) ∧
  (binaryCodeTerm 1 s t).realize (interpretation g0 P) ρ=formulaCode (.conj σ τ) ∧
  (binaryCodeTerm 2 s t).realize (interpretation g0 P) ρ=formulaCode (.disj σ τ)

def PositiveBooleanAxioms (g0 : Ground) : Prop := ∀ initial k,
  negAxiom.realize (stage g0 initial (k+1)) Fin.elim0 ∧
  impAxiom.realize (stage g0 initial (k+1)) Fin.elim0 ∧
  conjAxiom.realize (stage g0 initial (k+1)) Fin.elim0 ∧
  disjAxiom.realize (stage g0 initial (k+1)) Fin.elim0

end BooleanSpec

namespace Boolean
open GorbowSyntax GorbowBooleanTruth GorbowRegistryTuple GorbowSortedRevision GorbowSortedSyntaxCode

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ=header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as

theorem guardCalibration (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : BooleanSpec.GuardCalibration g0 := by
  intro n t P ρ
  change g0.universalRelation ((headerTerm 1 0 [t]).realize (interpretation g0 P) ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(relLaws (t.realize (interpretation g0 P) ρ) 0).1]
  exact GorbowSortedBooleanCodeProof.exactDomains.1 _

private theorem negRealize (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (s : Term n) P ρ :
    (negCodeTerm s).realize (interpretation g0 P) ρ =
      g0.universalFunction (header 1 0 [s.realize (interpretation g0 P) ρ]) := by
  change g0.universalFunction ((headerTerm 1 0 [s]).realize _ ρ)=_
  rw [headerRealize]
  rfl
private theorem binaryRealize (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (tag : Nat) (s t : Term n) P ρ :
    (binaryCodeTerm tag s t).realize (interpretation g0 P) ρ =
      g0.universalFunction (header 2 tag [s.realize (interpretation g0 P) ρ,t.realize (interpretation g0 P) ρ]) := by
  change g0.universalFunction ((headerTerm 2 tag [s,t]).realize _ ρ)=_
  rw [headerRealize]
  rfl

theorem functionCalibration (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : BooleanSpec.FunctionCalibration g0 := by
  intro n s t P ρ σ τ hs ht
  simp only [(negRealize g0 relLaws funLaws),(binaryRealize g0 relLaws funLaws),hs,ht]
  obtain ⟨hn,hi,hc,hd,ha,hx,hinst⟩ := funLaws (formulaCode σ) (formulaCode τ) 0
  rw [hn,hi,hc,hd]
  exact GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ

private theorem truthCodes (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) (initial : Extension) (k : Nat) (σ τ : Sentence) :
    (extensions g0 initial (k+1) (formulaCode (.neg σ)) ↔
      ¬ extensions g0 initial (k+1) (formulaCode σ)) ∧
    (extensions g0 initial (k+1) (formulaCode (.imp σ τ)) ↔
      (extensions g0 initial (k+1) (formulaCode σ) → extensions g0 initial (k+1) (formulaCode τ))) ∧
    (extensions g0 initial (k+1) (formulaCode (.conj σ τ)) ↔
      (extensions g0 initial (k+1) (formulaCode σ) ∧ extensions g0 initial (k+1) (formulaCode τ))) ∧
    (extensions g0 initial (k+1) (formulaCode (.disj σ τ)) ↔
      (extensions g0 initial (k+1) (formulaCode σ) ∨ extensions g0 initial (k+1) (formulaCode τ))) := by
  simpa [truthSentence,formulaQuote,Formula.realize,numeral_realize,stage,interpretation,GorbowRevisionSemantics.interpretation] using
    GorbowSortedRevisionCompositionProof.booleanTruth g0 initial k σ τ

private theorem instances (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) (initial : Extension) (k n : Nat) (s t : Term n) ρ
    (hs : (sentenceGuard s).realize (stage g0 initial (k+1)) ρ)
    (ht : (sentenceGuard t).realize (stage g0 initial (k+1)) ρ) :
    (biconditional (.truth (negCodeTerm s)) (.neg (.truth s))).realize (stage g0 initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 0 s t)) (.imp (.truth s) (.truth t))).realize (stage g0 initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 1 s t)) (.conj (.truth s) (.truth t))).realize (stage g0 initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 2 s t)) (.disj (.truth s) (.truth t))).realize (stage g0 initial (k+1)) ρ := by
  obtain ⟨σ,hσ⟩ := ((guardCalibration g0 relLaws funLaws) n s _ ρ).mp hs
  obtain ⟨τ,hτ⟩ := ((guardCalibration g0 relLaws funLaws) n t _ ρ).mp ht
  obtain ⟨hn,hi,hc,hd⟩ := (functionCalibration g0 relLaws funLaws) n s t _ ρ σ τ hσ hτ
  have hh := (truthCodes g0 relLaws funLaws) initial k σ τ
  simp only [stage,interpretation,GorbowRevisionSemantics.interpretation] at hn hi hc hd hσ hτ
  simpa only [biconditional,Formula.realize,hn,hi,hc,hd,hσ,hτ,stage,interpretation,GorbowRevisionSemantics.interpretation,iff_def] using hh

attribute [local irreducible] headerTerm pairTerm tupleTerm

private theorem closeBoolean (I : Interpretation)
    (h : ∀ (n : Nat) (s t : Term n) ρ,
      (sentenceGuard s).realize I ρ → (sentenceGuard t).realize I ρ →
    (biconditional (.truth (negCodeTerm s)) (.neg (.truth s))).realize I ρ ∧
    (biconditional (.truth (binaryCodeTerm 0 s t)) (.imp (.truth s) (.truth t))).realize I ρ ∧
    (biconditional (.truth (binaryCodeTerm 1 s t)) (.conj (.truth s) (.truth t))).realize I ρ ∧
    (biconditional (.truth (binaryCodeTerm 2 s t)) (.disj (.truth s) (.truth t))).realize I ρ) :
    negAxiom.realize I Fin.elim0 ∧ impAxiom.realize I Fin.elim0 ∧
    conjAxiom.realize I Fin.elim0 ∧ disjAxiom.realize I Fin.elim0 := by
  constructor
  · intro x hx
    exact (h 1 (.var 0) (.var 0) (Fin.cases x Fin.elim0) hx hx).1
  constructor
  · intro x y hxy
    exact (h 2 (.var 1) (.var 0) (Fin.cases y (Fin.cases x Fin.elim0)) hxy.1 hxy.2).2.1
  constructor
  · intro x y hxy
    exact (h 2 (.var 1) (.var 0) (Fin.cases y (Fin.cases x Fin.elim0)) hxy.1 hxy.2).2.2.1
  · intro x y hxy
    exact (h 2 (.var 1) (.var 0) (Fin.cases y (Fin.cases x Fin.elim0)) hxy.1 hxy.2).2.2.2

theorem positiveBooleanAxioms (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : BooleanSpec.PositiveBooleanAxioms g0 :=
  fun initial k => closeBoolean _ ((instances g0 relLaws funLaws) initial k)

end Boolean

namespace QuantifierSpec
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision GorbowFreeSupport GorbowNamedBinding
open GorbowFormulaComposition GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruth

def GuardDomains (g0 : Ground) : Prop := ∀ n (t : Term n) P ρ,
  ((variableGuard t).realize (interpretation g0 P) ρ ↔
    ∃ i,t.realize (interpretation g0 P) ρ=variableNumber i) ∧
  ((fullTermGuard t).realize (interpretation g0 P) ρ ↔
    ∃ s : Term 0,t.realize (interpretation g0 P) ρ=termCode s) ∧
  ((arithmeticTermGuard t).realize (interpretation g0 P) ρ ↔
    ∃ s : Term 0,t.realize (interpretation g0 P) ρ=termCode s ∧ ArithmeticTerm s)

def NamedDomain (g0 : Ground) : Prop := ∀ k (v f : Term k) P ρ,
  (namedGuard v f).realize (interpretation g0 P) ρ ↔
    ∃ (n : Nat) (φ : Formula n) (i : Fin n),
      v.realize (interpretation g0 P) ρ=variableNumber i.val ∧
      f.realize (interpretation g0 P) ρ=formulaCode φ ∧ formulaSupport φ={i.val}

def BindingFunctions (g0 : Ground) : Prop := ∀ n (φ : Formula n) (i : Fin n), formulaSupport φ={i.val} →
  ∀ k (v f : Term k) P ρ,
    v.realize (interpretation g0 P) ρ=variableNumber i.val →
    f.realize (interpretation g0 P) ρ=formulaCode φ →
    (allCodeTerm v f).realize (interpretation g0 P) ρ=formulaCode (bindAll i φ) ∧
    (exCodeTerm v f).realize (interpretation g0 P) ρ=formulaCode (bindEx i φ)

def InstanceFunction (g0 : Ground) : Prop := ∀ n (φ : Formula n) (i : Fin n), formulaSupport φ={i.val} →
  ∀ (s : Term 0) k (v f t : Term k) P ρ,
    v.realize (interpretation g0 P) ρ=variableNumber i.val →
    f.realize (interpretation g0 P) ρ=formulaCode φ →
    t.realize (interpretation g0 P) ρ=termCode s →
    (instanceCodeTerm v f t).realize (interpretation g0 P) ρ=formulaCode (namedClosedInstance i φ s)

def PositiveAxioms (g0 : Ground) : Prop := ∀ initial k,
  forallAxiom.realize (stage g0 initial (k+1)) Fin.elim0 ∧
  existsAxiom.realize (stage g0 initial (k+1)) Fin.elim0 ∧
  barcanAxiom.realize (stage g0 initial (k+1)) Fin.elim0

end QuantifierSpec

namespace Quantifier
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision GorbowFreeSupport GorbowNamedBinding
open GorbowFormulaComposition GorbowStandardInstances GorbowSortedQuantifierTruth GorbowRegistryTuple GorbowBooleanTruth

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ=header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as
private theorem variableRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (t : Term n) P ρ :
    (variableGuard t).realize (interpretation g0 P) ρ ↔
      GorbowSortedSyntaxCode.isVariableCode (t.realize (interpretation g0 P) ρ)=true := by
  change g0.universalRelation ((headerTerm 1 3 [t]).realize _ ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(relLaws (t.realize (interpretation g0 P) ρ) 0).2.2.2.1]
private theorem fullRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (t : Term n) P ρ :
    (fullTermGuard t).realize (interpretation g0 P) ρ ↔
      GorbowSortedBooleanCode.fullTermCode (t.realize (interpretation g0 P) ρ)=true := by
  change g0.universalRelation ((headerTerm 1 1 [t]).realize _ ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(relLaws (t.realize (interpretation g0 P) ρ) 0).2.1]
private theorem arithmeticRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (t : Term n) P ρ :
    (arithmeticTermGuard t).realize (interpretation g0 P) ρ ↔
      GorbowSortedBooleanCode.arithmeticTermCode (t.realize (interpretation g0 P) ρ)=true := by
  change g0.universalRelation ((headerTerm 1 2 [t]).realize _ ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(relLaws (t.realize (interpretation g0 P) ρ) 0).2.2.1]
private theorem namedRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (v f : Term n) P ρ :
    (namedGuard v f).realize (interpretation g0 P) ρ ↔
      GorbowSortedNamedCode.namedFormula (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ)=true := by
  change g0.universalRelation ((headerTerm 2 0 [v,f]).realize _ ρ) ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(relLaws (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ)).2.2.2.2]
private theorem allRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (v f : Term n) P ρ :
    (allCodeTerm v f).realize (interpretation g0 P) ρ =
      (GorbowSortedNamedCode.allNumber (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ)).getD 0 := by
  change g0.universalFunction ((headerTerm 2 3 [v,f]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (funLaws (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ) 0).2.2.2.2.1
private theorem exRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (v f : Term n) P ρ :
    (exCodeTerm v f).realize (interpretation g0 P) ρ =
      (GorbowSortedNamedCode.exNumber (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ)).getD 0 := by
  change g0.universalFunction ((headerTerm 2 4 [v,f]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (funLaws (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ) 0).2.2.2.2.2.1
private theorem instanceRaw (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) {n : Nat} (v f t : Term n) P ρ :
    (instanceCodeTerm v f t).realize (interpretation g0 P) ρ =
      (GorbowSortedNamedCode.instanceNumber (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ) (t.realize (interpretation g0 P) ρ)).getD 0 := by
  change g0.universalFunction ((headerTerm 3 0 [v,f,t]).realize _ ρ)=_
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  exact (funLaws (v.realize (interpretation g0 P) ρ) (f.realize (interpretation g0 P) ρ) (t.realize (interpretation g0 P) ρ)).2.2.2.2.2.2

theorem guardDomains (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : QuantifierSpec.GuardDomains g0 := by
  intro n t P ρ
  exact ⟨((variableRaw g0 relLaws funLaws) t P ρ).trans (GorbowSortedSyntaxCodeProof.actualCalibration.2.2.2.2 _),
    ((fullRaw g0 relLaws funLaws) t P ρ).trans (GorbowSortedBooleanCodeProof.exactDomains.2.1 _),
    ((arithmeticRaw g0 relLaws funLaws) t P ρ).trans (GorbowSortedBooleanCodeProof.exactDomains.2.2 _)⟩
theorem namedDomain (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : QuantifierSpec.NamedDomain g0 := by
  intro k v f P ρ
  exact ((namedRaw g0 relLaws funLaws) v f P ρ).trans (GorbowSortedNamedCodeProof.exactNamedDomain _ _)
theorem bindingFunctions (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : QuantifierSpec.BindingFunctions g0 := by
  intro n φ i hs k v f P ρ hv hf
  obtain ⟨ha,hx,hi⟩ := GorbowSortedNamedCodeProof.originalCalibration n φ i hs
  constructor
  · rw [(allRaw g0 relLaws funLaws),hv,hf,ha]; rfl
  · rw [(exRaw g0 relLaws funLaws),hv,hf,hx]; rfl
theorem instanceFunction (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : QuantifierSpec.InstanceFunction g0 := by
  intro n φ i hs s k v f t P ρ hv hf ht
  have hi := (GorbowSortedNamedCodeProof.originalCalibration n φ i hs).2.2 s
  rw [(instanceRaw g0 relLaws funLaws),hv,hf,ht,hi]
  rfl

private theorem truthAt (g : Ground) (initial : Extension) (k : Nat) (σ : Sentence) :
    (truthSentence σ).realize (stage g initial k) Fin.elim0 ↔ extensions g initial k (formulaCode σ) := by
  simp [truthSentence,formulaQuote,Formula.realize,numeral_realize,stage,interpretation,GorbowRevisionSemantics.interpretation]
private theorem knowledgeAt (g : Ground) (initial : Extension) (k a : Nat) (σ : Sentence) :
    (knowledgeSentence a σ).realize (stage g initial k) Fin.elim0 ↔ a=0 ∧ extensions g initial k (formulaCode σ) := by
  simp [knowledgeSentence,formulaQuote,Formula.realize,numeral_realize,stage,interpretation,GorbowRevisionSemantics.interpretation]

private theorem numericClauses (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) (initial : Extension) (k varCode code : Nat)
    (hn : GorbowSortedNamedCode.namedFormula varCode code=true) :
    (extensions g0 initial (k+1) ((GorbowSortedNamedCode.allNumber varCode code).getD 0) ↔
      ∀ t, GorbowSortedBooleanCode.fullTermCode t=true → extensions g0 initial (k+1) ((GorbowSortedNamedCode.instanceNumber varCode code t).getD 0)) ∧
    (extensions g0 initial (k+1) ((GorbowSortedNamedCode.exNumber varCode code).getD 0) ↔
      ∃ t, GorbowSortedBooleanCode.fullTermCode t=true ∧ extensions g0 initial (k+1) ((GorbowSortedNamedCode.instanceNumber varCode code t).getD 0)) ∧
    (∀ a, a=0 → (∀ t, GorbowSortedBooleanCode.arithmeticTermCode t=true →
      a=0 ∧ extensions g0 initial (k+1) ((GorbowSortedNamedCode.instanceNumber varCode code t).getD 0)) →
      a=0 ∧ extensions g0 initial (k+1) ((GorbowSortedNamedCode.allNumber varCode code).getD 0)) := by
  obtain ⟨n,φ,v,rfl,rfl,hs⟩ := (GorbowSortedNamedCodeProof.exactNamedDomain varCode code).mp hn
  obtain ⟨σ,τ,hσ,hτ,hq⟩ := GorbowSortedRevisionCompositionProof.namedQuantifiers n v φ hs
  obtain ⟨ha,hx,hi⟩ := GorbowSortedNamedCodeProof.originalCalibration n φ v hs
  have hca : (GorbowSortedNamedCode.allNumber (variableNumber v.val) (formulaCode φ)).getD 0=formulaCode σ := by rw [ha]; exact hσ.symm
  have hcx : (GorbowSortedNamedCode.exNumber (variableNumber v.val) (formulaCode φ)).getD 0=formulaCode τ := by rw [hx]; exact hτ.symm
  have hci (t : Term 0) : (GorbowSortedNamedCode.instanceNumber (variableNumber v.val) (formulaCode φ) (termCode t)).getD 0=formulaCode (namedClosedInstance v φ t) := by rw [hi t]; rfl
  have hqa := (hq g0 initial k).1
  have hqx := (hq g0 initial k).2.1
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
        (knowledgeSentence a (namedClosedInstance v φ t)).realize (stage g0 initial (k+1)) Fin.elim0 := by
      intro t ht
      apply (knowledgeAt _ _ _ _ _).mpr
      have hh := h (termCode t) ((GorbowSortedBooleanCodeProof.exactDomains.2.2 _).mpr ⟨t,rfl,ht⟩)
      simpa only [hci] using hh
    have hout := (hq g0 initial k).2.2 a ha0 htyped
    rw [hca]
    exact (knowledgeAt _ _ _ _ _).mp hout

attribute [local irreducible] headerTerm pairTerm tupleTerm

private theorem biconditionalAt {n : Nat} (φ ψ : Formula n) I ρ :
    (biconditional φ ψ).realize I ρ ↔ (φ.realize I ρ ↔ ψ.realize I ρ) := by
  simp only [biconditional,Formula.realize,iff_def]
private theorem truthTermAt (g0 : Ground) {n : Nat} (t : Term n) P ρ :
    (Formula.truth t).realize (interpretation g0 P) ρ ↔ P (t.realize (interpretation g0 P) ρ) := Iff.rfl
private theorem knowledgeTermAt (g0 : Ground) {n : Nat} (a t : Term n) P ρ :
    (Formula.knowledge a t).realize (interpretation g0 P) ρ ↔
      a.realize (interpretation g0 P) ρ=0 ∧ P (t.realize (interpretation g0 P) ρ) := Iff.rfl

private theorem forallRealization (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) (P : Extension) :
    forallAxiom.realize (interpretation g0 P) Fin.elim0 ↔
      ∀ v f, (isVariableCode v=true ∧ GorbowSortedNamedCode.namedFormula v f=true) →
        (P ((GorbowSortedNamedCode.allNumber v f).getD 0) ↔ ∀ t, GorbowSortedBooleanCode.fullTermCode t=true → P ((GorbowSortedNamedCode.instanceNumber v f t).getD 0)) := by
  apply forall_congr'
  intro v
  apply forall_congr'
  intro f
  apply imp_congr
  · apply and_congr
    · exact (variableRaw g0 relLaws funLaws) (.var 1) P (Fin.cases f (Fin.cases v Fin.elim0))
    · exact (namedRaw g0 relLaws funLaws) (.var 1) (.var 0) P (Fin.cases f (Fin.cases v Fin.elim0))
  · rw [biconditionalAt]
    apply iff_congr
    · rw [(truthTermAt g0),(allRaw g0 relLaws funLaws)]
      rfl
    · apply forall_congr'
      intro t
      apply imp_congr
      · exact (fullRaw g0 relLaws funLaws) (.var 0) P (Fin.cases t (Fin.cases f (Fin.cases v Fin.elim0)))
      · rw [(truthTermAt g0),(instanceRaw g0 relLaws funLaws)]
        rfl

private theorem existsRealization (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) (P : Extension) :
    existsAxiom.realize (interpretation g0 P) Fin.elim0 ↔
      ∀ v f, (isVariableCode v=true ∧ GorbowSortedNamedCode.namedFormula v f=true) →
        (P ((GorbowSortedNamedCode.exNumber v f).getD 0) ↔ ∃ t, GorbowSortedBooleanCode.fullTermCode t=true ∧ P ((GorbowSortedNamedCode.instanceNumber v f t).getD 0)) := by
  apply forall_congr'
  intro v
  apply forall_congr'
  intro f
  apply imp_congr
  · apply and_congr
    · exact (variableRaw g0 relLaws funLaws) (.var 1) P (Fin.cases f (Fin.cases v Fin.elim0))
    · exact (namedRaw g0 relLaws funLaws) (.var 1) (.var 0) P (Fin.cases f (Fin.cases v Fin.elim0))
  · rw [biconditionalAt]
    apply iff_congr
    · rw [(truthTermAt g0),(exRaw g0 relLaws funLaws)]
      rfl
    · apply exists_congr
      intro t
      apply and_congr
      · exact (fullRaw g0 relLaws funLaws) (.var 0) P (Fin.cases t (Fin.cases f (Fin.cases v Fin.elim0)))
      · rw [(truthTermAt g0),(instanceRaw g0 relLaws funLaws)]
        rfl

private theorem barcanRealization (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) (P : Extension) :
    barcanAxiom.realize (interpretation g0 P) Fin.elim0 ↔
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
    · exact (variableRaw g0 relLaws funLaws) (.var 1) P (Fin.cases f (Fin.cases v (Fin.cases a Fin.elim0)))
    · exact (namedRaw g0 relLaws funLaws) (.var 1) (.var 0) P (Fin.cases f (Fin.cases v (Fin.cases a Fin.elim0)))
  · apply imp_congr
    · apply forall_congr'
      intro t
      apply imp_congr
      · exact (arithmeticRaw g0 relLaws funLaws) (.var 0) P (Fin.cases t (Fin.cases f (Fin.cases v (Fin.cases a Fin.elim0))))
      · rw [(knowledgeTermAt g0),(instanceRaw g0 relLaws funLaws)]
        rfl
    · rw [(knowledgeTermAt g0),(allRaw g0 relLaws funLaws)]
      rfl

theorem positiveAxioms (g0 : Ground) (relLaws : RelationLaws g0) (funLaws : FunctionLaws g0) : QuantifierSpec.PositiveAxioms g0 := by
  intro initial k
  refine ⟨((forallRealization g0 relLaws funLaws) _).mpr ?_,((existsRealization g0 relLaws funLaws) _).mpr ?_,((barcanRealization g0 relLaws funLaws) _).mpr ?_⟩
  · intro v f h
    exact ((numericClauses g0 relLaws funLaws) initial k v f h.2).1
  · intro v f h
    exact ((numericClauses g0 relLaws funLaws) initial k v f h.2).2.1
  · intro a v f h
    exact ((numericClauses g0 relLaws funLaws) initial k v f h.2.2).2.2 a h.1

end Quantifier

theorem originalGround : Comparators.GorbowRegistryDispatch.OriginalGround := by
  constructor
  · intro a b
    obtain ⟨h0,h1,h2,h3,h4⟩ := GorbowSortedRegistryProof.relationDispatch a b
    change (_=true ↔ _) ∧ (_=true ↔ _) ∧ (_=true ↔ _) ∧ (_=true ↔ _) ∧ (_=true ↔ _)
    rw [h0,h1,h2,h3,h4]
    exact ⟨Iff.rfl,Iff.rfl,Iff.rfl,Iff.rfl,Iff.rfl⟩
  · exact GorbowSortedRegistryProof.functionDispatch

theorem gorbowRegistryDispatch : Comparators.GorbowRegistryDispatch.Target :=
  ⟨originalGround, Boolean.positiveBooleanAxioms, Quantifier.positiveAxioms⟩
end LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatchProof

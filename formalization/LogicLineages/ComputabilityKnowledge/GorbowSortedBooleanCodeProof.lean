module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedBooleanCode
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedTermCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedBooleanCode GorbowStandardInstances

private theorem evenMod (n : Nat) : tagFormula n%2=0 := by unfold tagFormula; omega
private theorem evenDiv (n : Nat) : tagFormula n/2=n := by unfold tagFormula; omega
private theorem oddMod (n : Nat) : tagTerm n%2=1 := by unfold tagTerm; omega
private theorem oddDiv (n : Nat) : tagTerm n/2=n := by unfold tagTerm; omega
private theorem legacyUnary (tag : Nat) (raw : List Nat) :
    GorbowBooleanRegistry.unaryNumber tag (GorbowCodeConstructors.number raw)=GorbowCodeConstructors.number (GorbowCodeConstructors.unary tag raw) :=
  GorbowBooleanRegistryProof.numericConstructors.1 tag raw
private theorem legacyBinary (tag : Nat) (a b : List Nat) :
    GorbowBooleanRegistry.binaryNumber tag (GorbowCodeConstructors.number a) (GorbowCodeConstructors.number b)=GorbowCodeConstructors.number (GorbowCodeConstructors.binary tag a b) :=
  GorbowBooleanRegistryProof.numericConstructors.2 tag a b

theorem rawConstructors : Comparators.GorbowSortedBooleanCode.RawConstructors := by
  constructor
  · intro tag raw
    simp [unaryNumber,formulaRawNumber,evenMod,evenDiv,legacyUnary]
  · intro tag a b
    simp [binaryNumber,formulaRawNumber,evenMod,evenDiv,legacyBinary]

theorem actualConstructors : Comparators.GorbowSortedBooleanCode.ActualConstructors := by
  intro n φ ψ
  have hu := rawConstructors.1 6 (GorbowFormulaPrefixCode.encode φ)
  have hi := rawConstructors.2 7 (GorbowFormulaPrefixCode.encode φ) (GorbowFormulaPrefixCode.encode ψ)
  have hc := rawConstructors.2 8 (GorbowFormulaPrefixCode.encode φ) (GorbowFormulaPrefixCode.encode ψ)
  have hd := rawConstructors.2 9 (GorbowFormulaPrefixCode.encode φ) (GorbowFormulaPrefixCode.encode ψ)
  exact ⟨hu,hi,hc,hd⟩

theorem exactDomains : Comparators.GorbowSortedBooleanCode.ExactDomains := by
  constructor
  · intro code
    simp only [sentenceCode,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨hp,h⟩
      obtain ⟨σ,hs⟩ := (GorbowBooleanRegistryProof.exactSentencehood (code/2)).mp h
      refine ⟨σ,?_⟩
      change code=2*GorbowCodeConstructors.formulaNumber σ
      omega
    · rintro ⟨σ,rfl⟩
      exact ⟨evenMod _,by rw [formulaCode,evenDiv]; exact (GorbowBooleanRegistryProof.exactSentencehood _).mpr ⟨σ,rfl⟩⟩
  constructor
  · intro code
    simp only [fullTermCode,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨hp,h⟩
      obtain ⟨t,ht⟩ := (GorbowClosedTermCodeProof.exactNumericDomains.1 (code/2)).mp h
      refine ⟨t,?_⟩
      change code=2*GorbowCodeConstructors.termNumber t+1
      omega
    · rintro ⟨t,rfl⟩
      exact ⟨oddMod _,by rw [termCode,oddDiv]; exact (GorbowClosedTermCodeProof.exactNumericDomains.1 _).mpr ⟨t,rfl⟩⟩
  · intro code
    simp only [arithmeticTermCode,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨hp,h⟩
      obtain ⟨t,ht,ha⟩ := (GorbowClosedTermCodeProof.exactNumericDomains.2 (code/2)).mp h
      refine ⟨t,?_,ha⟩
      change code=2*GorbowCodeConstructors.termNumber t+1
      omega
    · rintro ⟨t,rfl,ha⟩
      exact ⟨oddMod _,by rw [termCode,oddDiv]; exact (GorbowClosedTermCodeProof.exactNumericDomains.2 _).mpr ⟨t,rfl,ha⟩⟩

theorem wrongSortRejection : Comparators.GorbowSortedBooleanCode.WrongSortRejection := by
  refine ⟨?_,?_,?_⟩
  · intro n t tag
    simp [unaryNumber,sentenceCode,termCode,oddMod]
  · intro n t tag other
    simp [binaryNumber,termCode,oddMod]
  · intro n φ
    simp [fullTermCode,arithmeticTermCode,formulaCode,evenMod]

private theorem pr_div {α : Type} [Primcodable α] {f : α → Nat} (h : Primrec f) : Primrec (fun a => f a/2) :=
  Primrec.nat_div.comp h (Primrec.const 2)
private theorem pr_parity {α : Type} [Primcodable α] {f : α → Nat} (h : Primrec f) (k : Nat) : PrimrecPred (fun a => f a%2=k) :=
  Primrec.eq.comp (Primrec.nat_mod.comp h (Primrec.const 2)) (Primrec.const k)
private theorem pr_unary : Primrec (fun p : Nat × Nat => unaryNumber p.1 p.2) :=
  Primrec.ite (pr_parity Primrec.snd 0)
    (GorbowSortedSyntaxCodeProof.uniformPrograms.1.comp
      (GorbowBooleanRegistryProof.uniformPrograms.1.comp (Primrec.fst.pair (pr_div Primrec.snd)))) (Primrec.const 0)
private theorem pr_binary : Primrec (fun p : Nat × Nat × Nat => binaryNumber p.1 p.2.1 p.2.2) := by
  have ha : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite ((pr_parity ha 0).and (pr_parity hb 0))
    (GorbowSortedSyntaxCodeProof.uniformPrograms.1.comp
      (GorbowBooleanRegistryProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((pr_div ha).pair (pr_div hb))))) (Primrec.const 0)
private theorem pr_sentence : Primrec sentenceCode :=
  Primrec.and.comp (pr_parity Primrec.id 0).decide (GorbowBooleanRegistryProof.uniformPrograms.2.2.1.comp (pr_div Primrec.id))
private theorem pr_fullTerm : Primrec fullTermCode :=
  Primrec.and.comp (pr_parity Primrec.id 1).decide (GorbowClosedTermCodeProof.uniformPrograms.2.1.comp (pr_div Primrec.id))
private theorem pr_arithmeticTerm : Primrec arithmeticTermCode :=
  Primrec.and.comp (pr_parity Primrec.id 1).decide (GorbowClosedTermCodeProof.uniformPrograms.2.2.comp (pr_div Primrec.id))

theorem uniformPrograms : Comparators.GorbowSortedBooleanCode.UniformPrograms :=
  ⟨pr_unary,pr_binary,pr_sentence,pr_fullTerm,pr_arithmeticTerm⟩
theorem gorbowSortedBooleanCode : Comparators.GorbowSortedBooleanCode.Target :=
  ⟨rawConstructors,actualConstructors,exactDomains,wrongSortRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof

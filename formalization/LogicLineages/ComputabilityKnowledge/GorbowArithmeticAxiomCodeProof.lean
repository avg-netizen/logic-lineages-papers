module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticAxiomCode
public import LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCodeProof
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowSyntaxValidation GorbowInstanceCode
open GorbowLogicalAxiomCode (Annotation arg guardTerms)
open GorbowArithmeticAxiomCode

private theorem validTermEncode {n : Nat} (t : Term n) : validTerm n (GorbowTermPrefixCode.encode t) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.1 n _).mpr
    ⟨t,(GorbowTermPrefixCodeProof.decoderExact n _ t).mpr rfl⟩
private theorem inductionEncode (n : Nat) (φ : Formula (n+1)) :
    inductionCode n (GorbowFormulaPrefixCode.encode φ) = some (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.inductionAxiom φ)) :=
  (GorbowInstanceCodeProof.exactInduction n _ _).mpr ⟨φ,rfl,rfl⟩

private theorem encodedCompile (n : Nat) (w : ArithmeticInstance n) :
    compile n (encode w) = some (GorbowFormulaPrefixCode.encode (arithmeticFormula w)) := by
  cases w <;> simp [compile,encode,case0,case1,case2,case3,case4,case5,case6,guardTerms,arg,
    validTermEncode,inductionEncode,arithmeticFormula,GorbowFormulaPrefixCode.encode,
    GorbowTermPrefixCode.encode,binary,unary]

private theorem termOne (n : Nat) (args : List (List Nat)) (h : guardTerms n 1 args = true) :
    ∃ t : Term n, args = [GorbowTermPrefixCode.encode t] := by
  obtain ⟨hl,hv⟩ := (GorbowLogicalAxiomCodeProof.guardCalibration.2 n 1 args).mp h
  obtain ⟨raw,rfl⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨t,ht⟩ := hv raw (by simp)
  exact ⟨t,by simp [ht]⟩
private theorem termTwo (n : Nat) (args : List (List Nat)) (h : guardTerms n 2 args = true) :
    ∃ t u : Term n, args = [GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u] := by
  obtain ⟨hl,hv⟩ := (GorbowLogicalAxiomCodeProof.guardCalibration.2 n 2 args).mp h
  obtain ⟨rt,ru,rfl⟩ := List.length_eq_two.mp hl
  obtain ⟨t,ht⟩ := hv rt (by simp)
  obtain ⟨u,hu⟩ := hv ru (by simp)
  exact ⟨t,u,by simp [ht,hu]⟩

private theorem compilationDomain (n : Nat) (annotation : Annotation) (out : List Nat)
    (h : compile n annotation = some out) : ∃ w : ArithmeticInstance n, annotation = encode w := by
  rcases annotation with ⟨tag,args⟩
  by_cases ht : tag ≤ 6
  · interval_cases tag
    · have hc : case0 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 1 args = true := by
        by_contra hn
        simp [case0,hn] at hc
      obtain ⟨t,rfl⟩ := termOne n args hg
      exact ⟨.succNotZero t,rfl⟩
    · have hc : case1 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 2 args = true := by
        by_contra hn
        simp [case1,hn] at hc
      obtain ⟨t,u,rfl⟩ := termTwo n args hg
      exact ⟨.succInjective t u,rfl⟩
    · have hc : case2 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 1 args = true := by
        by_contra hn
        simp [case2,hn] at hc
      obtain ⟨t,rfl⟩ := termOne n args hg
      exact ⟨.addZero t,rfl⟩
    · have hc : case3 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 2 args = true := by
        by_contra hn
        simp [case3,hn] at hc
      obtain ⟨t,u,rfl⟩ := termTwo n args hg
      exact ⟨.addSucc t u,rfl⟩
    · have hc : case4 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 1 args = true := by
        by_contra hn
        simp [case4,hn] at hc
      obtain ⟨t,rfl⟩ := termOne n args hg
      exact ⟨.mulZero t,rfl⟩
    · have hc : case5 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 2 args = true := by
        by_contra hn
        simp [case5,hn] at hc
      obtain ⟨t,u,rfl⟩ := termTwo n args hg
      exact ⟨.mulSucc t u,rfl⟩
    · have hc : case6 n args = some out := by simpa [compile] using h
      have hl : args.length = 1 := by
        by_contra hn
        simp [case6,hn] at hc
      obtain ⟨raw,rfl⟩ := List.length_eq_one_iff.mp hl
      have hi : inductionCode n raw = some out := by simpa [case6,arg] using hc
      obtain ⟨φ,hφ,_⟩ := (GorbowInstanceCodeProof.exactInduction n raw out).mp hi
      exact ⟨.induction φ,by simp [encode,hφ]⟩
  · have h0 : tag ≠ 0 := by omega
    have h1 : tag ≠ 1 := by omega
    have h2 : tag ≠ 2 := by omega
    have h3 : tag ≠ 3 := by omega
    have h4 : tag ≠ 4 := by omega
    have h5 : tag ≠ 5 := by omega
    have h6 : tag ≠ 6 := by omega
    simp [compile,h0,h1,h2,h3,h4,h5,h6] at h

theorem exactCompilation : Comparators.GorbowArithmeticAxiomCode.ExactCompilation := by
  intro n annotation out
  constructor
  · intro h
    obtain ⟨w,rfl⟩ := compilationDomain n annotation out h
    rw [encodedCompile] at h
    exact ⟨w,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨w,rfl,rfl⟩
    exact encodedCompile n w

private theorem formulaEncodeEq {n : Nat} (a b : Formula n) :
    GorbowFormulaPrefixCode.encode a = GorbowFormulaPrefixCode.encode b ↔ a = b :=
  ⟨fun h => GorbowFormulaPrefixCodeProof.encodingInjective n h,fun h => congrArg GorbowFormulaPrefixCode.encode h⟩
private theorem termEncodeEq {n : Nat} (a b : Term n) :
    GorbowTermPrefixCode.encode a = GorbowTermPrefixCode.encode b ↔ a = b :=
  ⟨fun h => GorbowTermPrefixCodeProof.encodingInjective n h,fun h => congrArg GorbowTermPrefixCode.encode h⟩

theorem annotationInjection : Comparators.GorbowArithmeticAxiomCode.AnnotationInjection := by
  intro n a b h
  cases a <;> cases b <;> simp_all [encode,formulaEncodeEq,termEncodeEq]

private abbrev CaseInput := Nat × List (List Nat)
private theorem pr_arg (i : Nat) : Primrec (fun p : CaseInput => arg p.2 i) :=
  (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const i)
private theorem pr_unary {α : Type} [Primcodable α] (tag : Nat) {f : α → List Nat} (hf : Primrec f) :
    Primrec (fun x => unary tag (f x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const tag).pair hf)
private theorem pr_binary {α : Type} [Primcodable α] (tag : Nat) {f g : α → List Nat} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => binary tag (f x) (g x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp ((Primrec.const tag).pair (hf.pair hg))

private theorem pr_case0 : Primrec (fun p : CaseInput => case0 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (GorbowLogicalAxiomCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((Primrec.const 1).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_unary 6 (pr_binary 0 (pr_unary 2 (pr_arg 0)) (Primrec.const [1])))) (Primrec.const none)

private theorem pr_case1 : Primrec (fun p : CaseInput => case1 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (GorbowLogicalAxiomCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_binary 0 (pr_unary 2 (pr_arg 0)) (pr_unary 2 (pr_arg 1))) (pr_binary 0 (pr_arg 0) (pr_arg 1)))) (Primrec.const none)

private theorem pr_case2 : Primrec (fun p : CaseInput => case2 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (GorbowLogicalAxiomCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((Primrec.const 1).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 0 (pr_binary 3 (pr_arg 0) (Primrec.const [1])) (pr_arg 0))) (Primrec.const none)

private theorem pr_case3 : Primrec (fun p : CaseInput => case3 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (GorbowLogicalAxiomCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 0 (pr_binary 3 (pr_arg 0) (pr_unary 2 (pr_arg 1))) (pr_unary 2 (pr_binary 3 (pr_arg 0) (pr_arg 1))))) (Primrec.const none)

private theorem pr_case4 : Primrec (fun p : CaseInput => case4 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (GorbowLogicalAxiomCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((Primrec.const 1).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 0 (pr_binary 4 (pr_arg 0) (Primrec.const [1])) (Primrec.const [1]))) (Primrec.const none)

private theorem pr_case5 : Primrec (fun p : CaseInput => case5 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (GorbowLogicalAxiomCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 0 (pr_binary 4 (pr_arg 0) (pr_unary 2 (pr_arg 1))) (pr_binary 3 (pr_binary 4 (pr_arg 0) (pr_arg 1)) (pr_arg 0)))) (Primrec.const none)

private theorem pr_case6 : Primrec (fun p : CaseInput => case6 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))
    (GorbowInstanceCodeProof.uniformPrograms.2.2.2.2.comp (Primrec.fst.pair (pr_arg 0))) (Primrec.const none)

theorem uniformProgram : Comparators.GorbowArithmeticAxiomCode.UniformProgram := by
  have ht (i : Nat) : PrimrecPred (fun p : Nat × Annotation => p.2.1 = i) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const i)
  have hm : Primrec (fun p : Nat × Annotation => (p.1,p.2.2)) := Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  have h6 := Primrec.ite (ht 6) (pr_case6.comp hm) (Primrec.const (none : Option (List Nat)))
  have h5 := Primrec.ite (ht 5) (pr_case5.comp hm) h6
  have h4 := Primrec.ite (ht 4) (pr_case4.comp hm) h5
  have h3 := Primrec.ite (ht 3) (pr_case3.comp hm) h4
  have h2 := Primrec.ite (ht 2) (pr_case2.comp hm) h3
  have h1 := Primrec.ite (ht 1) (pr_case1.comp hm) h2
  have h0 := Primrec.ite (ht 0) (pr_case0.comp hm) h1
  exact h0

theorem gorbowArithmeticAxiomCode : Comparators.GorbowArithmeticAxiomCode.Target :=
  ⟨exactCompilation,annotationInjection,uniformProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCodeProof

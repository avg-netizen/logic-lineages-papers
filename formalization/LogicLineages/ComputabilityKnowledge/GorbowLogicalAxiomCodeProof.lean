module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowLogicalAxiomCode
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPACoreProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCodeProof
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowSyntaxValidation GorbowInstanceCode GorbowLogicalAxiomCode

private theorem validFormulaIff (n : Nat) (raw : List Nat) : validFormula n raw = true ↔
    ∃ φ : Formula n, raw = GorbowFormulaPrefixCode.encode φ := by
  rw [GorbowSyntaxValidationProof.exactTypedDomain.2 n raw]
  exact exists_congr (fun φ => GorbowFormulaPrefixCodeProof.decoderExact n raw φ)

private theorem validTermIff (n : Nat) (raw : List Nat) : validTerm n raw = true ↔
    ∃ t : Term n, raw = GorbowTermPrefixCode.encode t := by
  rw [GorbowSyntaxValidationProof.exactTypedDomain.1 n raw]
  exact exists_congr (fun t => GorbowTermPrefixCodeProof.decoderExact n raw t)

private theorem validFormulaEncode {n : Nat} (φ : Formula n) : validFormula n (GorbowFormulaPrefixCode.encode φ) = true :=
  (validFormulaIff n _).mpr ⟨φ,rfl⟩
private theorem validTermEncode {n : Nat} (t : Term n) : validTerm n (GorbowTermPrefixCode.encode t) = true :=
  (validTermIff n _).mpr ⟨t,rfl⟩

theorem guardCalibration : Comparators.GorbowLogicalAxiomCode.GuardCalibration := by
  constructor
  · intro n count args
    simp only [guardFormulas,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,validFormulaIff]
  · intro n count args
    simp only [guardTerms,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,validTermIff]

private theorem instEncode (n : Nat) (φ : Formula (n+1)) (t : Term n) :
    instanceCode n (GorbowFormulaPrefixCode.encode φ) (GorbowTermPrefixCode.encode t) =
      some (GorbowFormulaPrefixCode.encode (GorbowStandardInstances.instantiate φ t)) :=
  (GorbowInstanceCodeProof.exactInstance n _ _ _).mpr ⟨φ,t,rfl,rfl,rfl⟩

private theorem weakenEncode (n : Nat) (φ : Formula n) :
    weakeningCode n (GorbowFormulaPrefixCode.encode φ) = some (GorbowFormulaPrefixCode.encode (weaken φ)) :=
  (GorbowInstanceCodeProof.exactWeakening n _ _).mpr ⟨φ,rfl,rfl⟩

private theorem encodedCompile (n : Nat) (w : LogicalInstance n) :
    compile n (encode w) = some (GorbowFormulaPrefixCode.encode (logicalFormula w)) := by
  cases w <;>
    simp [compile,encode,case0,case1,case2,case3,case4,case5,case6,case7,case8,case9,
      case10,case11,case12,case13,case14,case15,guardFormulas,guardTerms,arg,
      validFormulaEncode,validTermEncode,instEncode,weakenEncode,
      logicalFormula,GorbowFormulaPrefixCode.encode,binary,unary]

private theorem formulaOne (n : Nat) (args : List (List Nat)) (h : guardFormulas n 1 args = true) :
    ∃ a : Formula n, args = [GorbowFormulaPrefixCode.encode a] := by
  obtain ⟨hl,hv⟩ := (guardCalibration.1 n 1 args).mp h
  obtain ⟨raw,rfl⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨a,ha⟩ := hv raw (by simp)
  exact ⟨a,by simp [ha]⟩

private theorem formulaTwo (n : Nat) (args : List (List Nat)) (h : guardFormulas n 2 args = true) :
    ∃ a b : Formula n, args = [GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b] := by
  obtain ⟨hl,hv⟩ := (guardCalibration.1 n 2 args).mp h
  obtain ⟨ra,rb,rfl⟩ := List.length_eq_two.mp hl
  obtain ⟨a,ha⟩ := hv ra (by simp)
  obtain ⟨b,hb⟩ := hv rb (by simp)
  exact ⟨a,b,by simp [ha,hb]⟩

private theorem formulaThree (n : Nat) (args : List (List Nat)) (h : guardFormulas n 3 args = true) :
    ∃ a b c : Formula n, args = [GorbowFormulaPrefixCode.encode a,GorbowFormulaPrefixCode.encode b,GorbowFormulaPrefixCode.encode c] := by
  obtain ⟨hl,hv⟩ := (guardCalibration.1 n 3 args).mp h
  obtain ⟨ra,rb,rc,rfl⟩ := List.length_eq_three.mp hl
  obtain ⟨a,ha⟩ := hv ra (by simp)
  obtain ⟨b,hb⟩ := hv rb (by simp)
  obtain ⟨c,hc⟩ := hv rc (by simp)
  exact ⟨a,b,c,by simp [ha,hb,hc]⟩

private theorem termOne (n : Nat) (args : List (List Nat)) (h : guardTerms n 1 args = true) :
    ∃ t : Term n, args = [GorbowTermPrefixCode.encode t] := by
  obtain ⟨hl,hv⟩ := (guardCalibration.2 n 1 args).mp h
  obtain ⟨raw,rfl⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨t,ht⟩ := hv raw (by simp)
  exact ⟨t,by simp [ht]⟩

private theorem compilationDomain (n : Nat) (annotation : Annotation) (out : List Nat)
    (h : compile n annotation = some out) : ∃ w : LogicalInstance n, annotation = encode w := by
  rcases annotation with ⟨tag,args⟩
  by_cases ht : tag ≤ 15
  · interval_cases tag
    · have hc : case0 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case0,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.k a b,rfl⟩
    · have hc : case1 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 3 args = true := by
        by_contra hn
        simp [case1,hn] at hc
      obtain ⟨a,b,c,rfl⟩ := formulaThree n args hg
      exact ⟨.s a b c,rfl⟩
    · have hc : case2 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case2,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.classicalContraposition a b,rfl⟩
    · have hc : case3 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case3,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.andLeft a b,rfl⟩
    · have hc : case4 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case4,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.andRight a b,rfl⟩
    · have hc : case5 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case5,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.andIntro a b,rfl⟩
    · have hc : case6 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case6,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.orLeft a b,rfl⟩
    · have hc : case7 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 2 args = true := by
        by_contra hn
        simp [case7,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo n args hg
      exact ⟨.orRight a b,rfl⟩
    · have hc : case8 n args = some out := by simpa [compile] using h
      have hg : guardFormulas n 3 args = true := by
        by_contra hn
        simp [case8,hn] at hc
      obtain ⟨a,b,c,rfl⟩ := formulaThree n args hg
      exact ⟨.orElim a b c,rfl⟩
    · have hc : case9 n args = some out := by simpa [compile] using h
      have hg : guardFormulas (n+1) 1 args = true := by
        by_contra hn
        simp [case9,hn] at hc
      obtain ⟨a,rfl⟩ := formulaOne (n+1) args hg
      exact ⟨.existsDualForward a,rfl⟩
    · have hc : case10 n args = some out := by simpa [compile] using h
      have hg : guardFormulas (n+1) 1 args = true := by
        by_contra hn
        simp [case10,hn] at hc
      obtain ⟨a,rfl⟩ := formulaOne (n+1) args hg
      exact ⟨.existsDualBackward a,rfl⟩
    · have hc : case11 n args = some out := by simpa [compile] using h
      have hg : guardTerms n 1 args = true := by
        by_contra hn
        simp [case11,hn] at hc
      obtain ⟨t,rfl⟩ := termOne n args hg
      exact ⟨.reflexive t,rfl⟩
    · have hc : case12 n args = some out := by simpa [compile] using h
      have hl : args.length = 3 := by
        by_contra hn
        simp [case12,hn] at hc
      obtain ⟨a,t,u,rfl⟩ := List.length_eq_three.mp hl
      simp only [case12,List.length_cons,List.length_nil,↓reduceIte,arg,List.getD_cons_zero,List.getD_cons_succ] at hc
      cases ha : instanceCode n a t with
      | none => simp [ha] at hc
      | some left =>
          cases hb : instanceCode n a u with
          | none => simp [ha,hb] at hc
          | some right =>
              obtain ⟨φ,tt,hφ,htt,_⟩ := (GorbowInstanceCodeProof.exactInstance n a t left).mp ha
              obtain ⟨ψ,uu,hψ,huu,_⟩ := (GorbowInstanceCodeProof.exactInstance n a u right).mp hb
              exact ⟨.equalityReplace φ tt uu,by simp [encode,hφ,htt,huu]⟩
    · have hc : case13 n args = some out := by simpa [compile] using h
      have hl : args.length = 2 := by
        by_contra hn
        simp [case13,hn] at hc
      obtain ⟨a,t,rfl⟩ := List.length_eq_two.mp hl
      simp only [case13,List.length_cons,List.length_nil,↓reduceIte,arg,List.getD_cons_zero,List.getD_cons_succ] at hc
      cases ha : instanceCode n a t with
      | none => simp [ha] at hc
      | some inst =>
          obtain ⟨φ,tt,hφ,htt,_⟩ := (GorbowInstanceCodeProof.exactInstance n a t inst).mp ha
          exact ⟨.allInstantiate φ tt,by simp [encode,hφ,htt]⟩
    · have hc : case14 n args = some out := by simpa [compile] using h
      have hg : guardFormulas (n+1) 2 args = true := by
        by_contra hn
        simp [case14,hn] at hc
      obtain ⟨a,b,rfl⟩ := formulaTwo (n+1) args hg
      exact ⟨.allDistribute a b,rfl⟩
    · have hc : case15 n args = some out := by simpa [compile] using h
      have hl : args.length = 1 := by
        by_contra hn
        simp [case15,hn] at hc
      obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hl
      simp only [case15,List.length_cons,List.length_nil,↓reduceIte,arg,List.getD_cons_zero] at hc
      cases ha : weakeningCode n a with
      | none => simp [ha] at hc
      | some shifted =>
          obtain ⟨φ,hφ,_⟩ := (GorbowInstanceCodeProof.exactWeakening n a shifted).mp ha
          exact ⟨.allVacuous φ,by simp [encode,hφ]⟩
  · have h0 : tag ≠ 0 := by omega
    have h1 : tag ≠ 1 := by omega
    have h2 : tag ≠ 2 := by omega
    have h3 : tag ≠ 3 := by omega
    have h4 : tag ≠ 4 := by omega
    have h5 : tag ≠ 5 := by omega
    have h6 : tag ≠ 6 := by omega
    have h7 : tag ≠ 7 := by omega
    have h8 : tag ≠ 8 := by omega
    have h9 : tag ≠ 9 := by omega
    have h10 : tag ≠ 10 := by omega
    have h11 : tag ≠ 11 := by omega
    have h12 : tag ≠ 12 := by omega
    have h13 : tag ≠ 13 := by omega
    have h14 : tag ≠ 14 := by omega
    have h15 : tag ≠ 15 := by omega
    simp [compile,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15] at h

theorem exactCompilation : Comparators.GorbowLogicalAxiomCode.ExactCompilation := by
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

theorem annotationInjection : Comparators.GorbowLogicalAxiomCode.AnnotationInjection := by
  intro n a b h
  cases a <;> cases b <;> simp_all [encode,formulaEncodeEq,termEncodeEq]

private theorem pr_allValid (valid : Nat → List Nat → Bool)
    (hv : Primrec (fun p : Nat × List Nat => valid p.1 p.2)) :
    Primrec (fun p : Nat × List (List Nat) => p.2.all (fun raw => valid p.1 raw)) := by
  have hp : PrimrecRel (fun raw : List Nat => fun n : Nat => valid n raw = true) :=
    Primrec.eq.comp (hv.comp (Primrec.snd.pair Primrec.fst)) (Primrec.const true)
  have h := hp.forall_mem_list.decide.comp Primrec.snd Primrec.fst
  apply h.of_eq
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.all_eq_true]

private theorem pr_guard (valid : Nat → List Nat → Bool)
    (hv : Primrec (fun p : Nat × List Nat => valid p.1 p.2)) :
    Primrec (fun p : Nat × Nat × List (List Nat) =>
      decide (p.2.2.length = p.2.1) && p.2.2.all (fun raw => valid p.1 raw)) :=
  Primrec.and.comp
    (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd)).decide
    ((pr_allValid valid hv).comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))

private theorem pr_guardFormulas : Primrec (fun p : Nat × Nat × List (List Nat) => guardFormulas p.1 p.2.1 p.2.2) :=
  pr_guard validFormula GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2
private theorem pr_guardTerms : Primrec (fun p : Nat × Nat × List (List Nat) => guardTerms p.1 p.2.1 p.2.2) :=
  pr_guard validTerm GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1

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
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_arg 0) (pr_binary 7 (pr_arg 1) (pr_arg 0)))) (Primrec.const none)

private theorem pr_case1 : Primrec (fun p : CaseInput => case1 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 3).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_binary 7 (pr_arg 0) (pr_binary 7 (pr_arg 1) (pr_arg 2))) (pr_binary 7 (pr_binary 7 (pr_arg 0) (pr_arg 1)) (pr_binary 7 (pr_arg 0) (pr_arg 2))))) (Primrec.const none)

private theorem pr_case2 : Primrec (fun p : CaseInput => case2 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_binary 7 (pr_unary 6 (pr_arg 0)) (pr_unary 6 (pr_arg 1))) (pr_binary 7 (pr_arg 1) (pr_arg 0)))) (Primrec.const none)

private theorem pr_case3 : Primrec (fun p : CaseInput => case3 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_binary 8 (pr_arg 0) (pr_arg 1)) (pr_arg 0))) (Primrec.const none)

private theorem pr_case4 : Primrec (fun p : CaseInput => case4 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_binary 8 (pr_arg 0) (pr_arg 1)) (pr_arg 1))) (Primrec.const none)

private theorem pr_case5 : Primrec (fun p : CaseInput => case5 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_arg 0) (pr_binary 7 (pr_arg 1) (pr_binary 8 (pr_arg 0) (pr_arg 1))))) (Primrec.const none)

private theorem pr_case6 : Primrec (fun p : CaseInput => case6 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_arg 0) (pr_binary 9 (pr_arg 0) (pr_arg 1)))) (Primrec.const none)

private theorem pr_case7 : Primrec (fun p : CaseInput => case7 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_arg 1) (pr_binary 9 (pr_arg 0) (pr_arg 1)))) (Primrec.const none)

private theorem pr_case8 : Primrec (fun p : CaseInput => case8 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp (Primrec.fst.pair ((Primrec.const 3).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_binary 7 (pr_arg 0) (pr_arg 2)) (pr_binary 7 (pr_binary 7 (pr_arg 1) (pr_arg 2)) (pr_binary 7 (pr_binary 9 (pr_arg 0) (pr_arg 1)) (pr_arg 2))))) (Primrec.const none)

private theorem pr_case9 : Primrec (fun p : CaseInput => case9 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp ((Primrec.succ.comp Primrec.fst).pair ((Primrec.const 1).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_unary 11 (pr_arg 0)) (pr_unary 6 (pr_unary 10 (pr_unary 6 (pr_arg 0)))))) (Primrec.const none)

private theorem pr_case10 : Primrec (fun p : CaseInput => case10 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp ((Primrec.succ.comp Primrec.fst).pair ((Primrec.const 1).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_unary 6 (pr_unary 10 (pr_unary 6 (pr_arg 0)))) (pr_unary 11 (pr_arg 0)))) (Primrec.const none)

private theorem pr_case11 : Primrec (fun p : CaseInput => case11 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardTerms.comp (Primrec.fst.pair ((Primrec.const 1).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 0 (pr_arg 0) (pr_arg 0))) (Primrec.const none)

private theorem pr_case14 : Primrec (fun p : CaseInput => case14 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp
    (pr_guardFormulas.comp ((Primrec.succ.comp Primrec.fst).pair ((Primrec.const 2).pair Primrec.snd))) (Primrec.const true))
    (Primrec.option_some.comp (pr_binary 7 (pr_unary 10 (pr_binary 7 (pr_arg 0) (pr_arg 1))) (pr_binary 7 (pr_unary 10 (pr_arg 0)) (pr_unary 10 (pr_arg 1))))) (Primrec.const none)

private theorem pr_instAt (i : Nat) : Primrec (fun p : CaseInput => instanceCode p.1 (arg p.2 0) (arg p.2 i)) :=
  GorbowInstanceCodeProof.uniformPrograms.2.1.comp (Primrec.fst.pair ((pr_arg 0).pair (pr_arg i)))

private theorem pr_case12Assembly : Primrec (fun p : (CaseInput × List Nat) × List Nat =>
    some (binary 7 (binary 0 (arg p.1.1.2 1) (arg p.1.1.2 2)) (binary 7 p.1.2 p.2))) :=
  Primrec.option_some.comp
    (pr_binary 7 (pr_binary 0 ((pr_arg 1).comp (Primrec.fst.comp Primrec.fst))
      ((pr_arg 2).comp (Primrec.fst.comp Primrec.fst)))
      (pr_binary 7 (Primrec.snd.comp Primrec.fst) Primrec.snd))

private theorem pr_case12Body : Primrec (fun p : CaseInput => do
    let left ← instanceCode p.1 (arg p.2 0) (arg p.2 1)
    let right ← instanceCode p.1 (arg p.2 0) (arg p.2 2)
    some (binary 7 (binary 0 (arg p.2 1) (arg p.2 2)) (binary 7 left right))) := by
  have hi := Primrec.option_bind ((pr_instAt 2).comp Primrec.fst) pr_case12Assembly.to₂
  have h := Primrec.option_bind (pr_instAt 1) hi.to₂
  exact h.of_eq (fun _ => rfl)

private theorem pr_case12 : Primrec (fun p : CaseInput => case12 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 3))
    pr_case12Body (Primrec.const none)

private theorem pr_case13Body : Primrec (fun p : CaseInput => do
    let inst ← instanceCode p.1 (arg p.2 0) (arg p.2 1)
    some (binary 7 (unary 10 (arg p.2 0)) inst)) := by
  have ha : Primrec (fun p : CaseInput × List Nat => some (binary 7 (unary 10 (arg p.1.2 0)) p.2)) :=
    Primrec.option_some.comp (pr_binary 7 (pr_unary 10 ((pr_arg 0).comp Primrec.fst)) Primrec.snd)
  exact Primrec.option_bind (pr_instAt 1) ha.to₂

private theorem pr_case13 : Primrec (fun p : CaseInput => case13 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
    pr_case13Body (Primrec.const none)

private theorem pr_case15Body : Primrec (fun p : CaseInput => do
    let shifted ← weakeningCode p.1 (arg p.2 0)
    some (binary 7 (arg p.2 0) (unary 10 shifted))) := by
  have hw := GorbowInstanceCodeProof.uniformPrograms.2.2.1.comp (Primrec.fst.pair (pr_arg 0))
  have ha : Primrec (fun p : CaseInput × List Nat => some (binary 7 (arg p.1.2 0) (unary 10 p.2))) :=
    Primrec.option_some.comp (pr_binary 7 ((pr_arg 0).comp Primrec.fst) (pr_unary 10 Primrec.snd))
  exact Primrec.option_bind hw ha.to₂

private theorem pr_case15 : Primrec (fun p : CaseInput => case15 p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))
    pr_case15Body (Primrec.const none)

private theorem pr_compile : Primrec (fun p : Nat × Annotation => compile p.1 p.2) := by
  have ht (i : Nat) : PrimrecPred (fun p : Nat × Annotation => p.2.1 = i) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const i)
  have hm : Primrec (fun p : Nat × Annotation => (p.1,p.2.2)) := Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  have h15 := Primrec.ite (ht 15) (pr_case15.comp hm) (Primrec.const (none : Option (List Nat)))
  have h14 := Primrec.ite (ht 14) (pr_case14.comp hm) h15
  have h13 := Primrec.ite (ht 13) (pr_case13.comp hm) h14
  have h12 := Primrec.ite (ht 12) (pr_case12.comp hm) h13
  have h11 := Primrec.ite (ht 11) (pr_case11.comp hm) h12
  have h10 := Primrec.ite (ht 10) (pr_case10.comp hm) h11
  have h9 := Primrec.ite (ht 9) (pr_case9.comp hm) h10
  have h8 := Primrec.ite (ht 8) (pr_case8.comp hm) h9
  have h7 := Primrec.ite (ht 7) (pr_case7.comp hm) h8
  have h6 := Primrec.ite (ht 6) (pr_case6.comp hm) h7
  have h5 := Primrec.ite (ht 5) (pr_case5.comp hm) h6
  have h4 := Primrec.ite (ht 4) (pr_case4.comp hm) h5
  have h3 := Primrec.ite (ht 3) (pr_case3.comp hm) h4
  have h2 := Primrec.ite (ht 2) (pr_case2.comp hm) h3
  have h1 := Primrec.ite (ht 1) (pr_case1.comp hm) h2
  have h0 := Primrec.ite (ht 0) (pr_case0.comp hm) h1
  exact h0

theorem uniformPrograms : Comparators.GorbowLogicalAxiomCode.UniformPrograms :=
  ⟨pr_guardFormulas,pr_guardTerms,pr_compile⟩

theorem gorbowLogicalAxiomCode : Comparators.GorbowLogicalAxiomCode.Target :=
  ⟨guardCalibration,exactCompilation,annotationInjection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCodeProof

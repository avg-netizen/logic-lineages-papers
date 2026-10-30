module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowProofChecker
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowProofChecker

private theorem lineParts {h : History} {l : Line} (hc : lineCheck h l = true) :
    GorbowSyntaxValidation.validFormula (context l) (conclusion l) = true ∧ ruleCheck h l = true := by
  simpa [lineCheck] using hc

private theorem mpInfo {h : History} {l : Line} (hc : ruleCheck h l = true) (hr : rule l = 2) :
    ∃ a b, h[(payload l).2.2.1]? = some a ∧ h[(payload l).2.2.2]? = some b ∧
      a.1 = context l ∧ b.1 = context l ∧ a.2 = binary 7 b.2 (conclusion l) := by
  simp only [ruleCheck,hr,show (2:Nat) ≠ 0 by omega,show (2:Nat) ≠ 1 by omega,if_false,if_true] at hc
  split at hc
  · cases ha : h[(payload l).2.2.1]? with
    | none => simp [ha] at hc
    | some a =>
      cases hb : h[(payload l).2.2.2]? with
      | none => simp [ha,hb] at hc
      | some b => exact ⟨a,b,rfl,rfl,by simpa [ha,hb] using hc⟩
  · simp at hc

private theorem genInfo {h : History} {l : Line} (hc : ruleCheck h l = true) (hr : rule l = 3) :
    ∃ a, h[(payload l).2.2.1]? = some a ∧ a.1 = context l+1 ∧ conclusion l = unary 10 a.2 := by
  simp only [ruleCheck,hr,show (3:Nat) ≠ 0 by omega,show (3:Nat) ≠ 1 by omega,
    show (3:Nat) ≠ 2 by omega,if_false,if_true] at hc
  split at hc
  · cases ha : h[(payload l).2.2.1]? with
    | none => simp [ha] at hc
    | some a => exact ⟨a,rfl,by simpa [ha] using hc⟩
  · simp at hc

theorem referenceBounds : Comparators.GorbowProofChecker.ReferenceBounds := by
  intro h l hc
  have hp := (lineParts hc).2
  constructor
  · intro hr
    obtain ⟨a,b,ha,hb,_⟩ := mpInfo hp hr
    exact ⟨(List.getElem?_eq_some_iff.mp ha).1,(List.getElem?_eq_some_iff.mp hb).1⟩
  · intro hr
    obtain ⟨a,ha,_⟩ := genInfo hp hr
    exact (List.getElem?_eq_some_iff.mp ha).1

private theorem foldNone (ls : List Line) : ls.foldl step none = none := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simpa [List.foldl,step] using ih

theorem runConcatenation : Comparators.GorbowProofChecker.RunConcatenation := by
  intro h a b
  simp only [run,List.foldl_append]
  cases a.foldl step (some h) <;> simp [foldNone]

private theorem runAppend (h : History) (a b : List Line) :
    run h (a++b) = (run h a).bind (fun next => run next b) := runConcatenation h a b

private theorem lineSound {h : History} (hs : SoundHistory h) (l : Line) (hc : lineCheck h l = true) :
    ∃ φ : Formula (context l), conclusion l = GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Proof φ) := by
  obtain ⟨hv,hr⟩ := lineParts hc
  obtain ⟨φ,hφ⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mp hv
  have he : conclusion l = GorbowFormulaPrefixCode.encode φ :=
    (GorbowFormulaPrefixCodeProof.decoderExact _ _ φ).mp hφ
  by_cases h0 : rule l = 0
  · have hh : (payload l).2.2.1 = 0 ∧ (payload l).2.2.2 = 0 ∧
        GorbowLogicalAxiomCode.compile (context l) ((payload l).1,(payload l).2.1) = some (conclusion l) := by
      simpa [ruleCheck,h0] using hr
    obtain ⟨w,_,hw⟩ := (GorbowLogicalAxiomCodeProof.exactCompilation _ _ _).mp hh.2.2
    exact ⟨logicalFormula w,hw,⟨.logical w⟩⟩
  by_cases h1 : rule l = 1
  · have hh : (payload l).2.2.1 = 0 ∧ (payload l).2.2.2 = 0 ∧
        GorbowArithmeticAxiomCode.compile (context l) ((payload l).1,(payload l).2.1) = some (conclusion l) := by
      simpa [ruleCheck,h0,h1] using hr
    obtain ⟨w,_,hw⟩ := (GorbowArithmeticAxiomCodeProof.exactCompilation _ _ _).mp hh.2.2
    exact ⟨arithmeticFormula w,hw,⟨.arithmetic w⟩⟩
  by_cases h2 : rule l = 2
  · obtain ⟨⟨na,ra⟩,⟨nb,rb⟩,ha,hb,ea,eb,eab⟩ := mpInfo hr h2
    dsimp at ea eb eab
    subst na; subst nb
    obtain ⟨a,hea,⟨pa⟩⟩ := hs _ (List.mem_of_getElem? ha)
    obtain ⟨b,heb,⟨pb⟩⟩ := hs _ (List.mem_of_getElem? hb)
    dsimp at hea heb
    have eqf : a = .imp b φ := GorbowFormulaPrefixCodeProof.encodingInjective _ (by
      simpa [GorbowFormulaPrefixCode.encode,binary,hea,heb,he] using eab)
    subst a
    exact ⟨φ,he,⟨.mp pa pb⟩⟩
  by_cases h3 : rule l = 3
  · obtain ⟨⟨na,ra⟩,ha,ea,er⟩ := genInfo hr h3
    dsimp at ea er
    subst na
    obtain ⟨a,hea,⟨pa⟩⟩ := hs _ (List.mem_of_getElem? ha)
    dsimp at hea
    exact ⟨.all a,by simpa [GorbowFormulaPrefixCode.encode,unary,hea] using er,⟨.generalize pa⟩⟩
  simp [ruleCheck,h0,h1,h2,h3] at hr

theorem historySoundness : Comparators.GorbowProofChecker.HistorySoundness := by
  intro h hs ls
  induction ls generalizing h with
  | nil => intro next hn; cases hn; exact hs
  | cons l ls ih =>
    intro next hn
    by_cases hc : lineCheck h l = true
    · have hnew : SoundHistory ((context l,conclusion l)::h) := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact lineSound hs l hc
        · exact hs e he
      apply ih _ hnew next
      simpa [run,List.foldl,step,hc] using hn
    · simp [run,List.foldl,step,hc,foldNone] at hn

private theorem validEncode {n : Nat} (φ : Formula n) :
    GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode φ) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mpr
    ⟨φ,(GorbowFormulaPrefixCodeProof.decoderExact _ _ φ).mpr rfl⟩
private theorem logicalChecked {n : Nat} (w : LogicalInstance n) (h : History) :
    lineCheck h (logicalLine w) = true := by
  have hw := (GorbowLogicalAxiomCodeProof.exactCompilation n _ _).mpr ⟨w,rfl,rfl⟩
  simpa [lineCheck,logicalLine,context,conclusion,ruleCheck,rule,payload,validEncode] using hw
private theorem arithmeticChecked {n : Nat} (w : ArithmeticInstance n) (h : History) :
    lineCheck h (arithmeticLine w) = true := by
  have hw := (GorbowArithmeticAxiomCodeProof.exactCompilation n _ _).mpr ⟨w,rfl,rfl⟩
  simpa [lineCheck,arithmeticLine,context,conclusion,ruleCheck,rule,payload,validEncode] using hw

private theorem conclusionLength (ls : List Line) : (lineConclusions ls).length = ls.length := by
  simp [lineConclusions]

theorem compilationShape : Comparators.GorbowProofChecker.CompilationShape := by
  intro n φ p
  cases p <;> simp [proofLines,lineConclusions,logicalLine,arithmeticLine,mpLine,generalizeLine,
    context,conclusion,List.reverse_append,List.map_append,List.length_append]

private theorem getZeroAppend {xs ys : History} {e : Entry} (h : xs.head? = some e) :
    (xs++ys)[0]? = some e := by
  cases xs <;> simp_all
private theorem getLengthAppend {xs ys zs : History} {e : Entry} (h : ys.head? = some e) :
    (xs++ys++zs)[xs.length]? = some e := by
  induction xs with
  | nil => simpa using getZeroAppend (ys := zs) h
  | cons a xs ih => simpa using ih

theorem compilationCorrectness : Comparators.GorbowProofChecker.CompilationCorrectness := by
  intro n φ p
  induction p with
  | logical w =>
    intro h
    simp [proofLines,run,step,logicalChecked,lineConclusions]
  | arithmetic w =>
    intro h
    simp [proofLines,run,step,arithmeticChecked,lineConclusions]
  | @mp n a b p q ihp ihq =>
    intro h
    let hp := lineConclusions (proofLines p)
    let hq := lineConclusions (proofLines q)
    have ep : (hq++hp++h)[(proofLines q).length]? = some (n,GorbowFormulaPrefixCode.encode (.imp a b)) := by
      rw [← conclusionLength (proofLines q)]
      exact getLengthAppend (compilationShape _ _ p).2
    have eq : (hq++hp++h)[0]? = some (n,GorbowFormulaPrefixCode.encode a) := by
      simpa [List.append_assoc] using getZeroAppend (ys := hp++h) (compilationShape _ _ q).2
    simp only [List.append_assoc] at ep eq
    have hc : lineCheck (hq++hp++h) (mpLine n (GorbowFormulaPrefixCode.encode b) (proofLines q).length 0) = true := by
      simp [lineCheck,mpLine,context,conclusion,ruleCheck,rule,payload,validEncode,ep,eq,
        GorbowFormulaPrefixCode.encode,binary]
    rw [proofLines,runAppend,runAppend,ihp]
    simp only [Option.bind_some]
    rw [ihq]
    simp only [Option.bind_some]
    have hc' : lineCheck (hq++(hp++h)) (mpLine n (GorbowFormulaPrefixCode.encode b) (proofLines q).length 0) = true := by
      simpa only [List.append_assoc] using hc
    change run (hq++(hp++h)) [_] = _
    simp only [run,List.foldl,step,Option.bind_some,hc',if_true]
    congr 1
    simp [lineConclusions,List.reverse_append,List.map_append,List.append_assoc,hp,hq]
    simpa [lineConclusions,hp,hq,List.append_assoc] using hc
  | @generalize n a p ih =>
    intro h
    have ep : (lineConclusions (proofLines p)++h)[0]? = some (n+1,GorbowFormulaPrefixCode.encode a) :=
      getZeroAppend (compilationShape _ _ p).2
    have hc : lineCheck (lineConclusions (proofLines p)++h)
        (generalizeLine n (GorbowFormulaPrefixCode.encode (.all a)) 0) = true := by
      change (GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode (.all a)) && _) = true
      rw [validEncode]
      simp [ruleCheck,generalizeLine,context,conclusion,rule,payload,ep,GorbowFormulaPrefixCode.encode,unary]
    rw [proofLines,runAppend,ih]
    simp only [Option.bind_some]
    simp only [run,List.foldl,step,Option.bind_some,hc,if_true]
    congr 1
    simp [lineConclusions,List.reverse_append,List.map_append,List.append_assoc]
    simpa [lineConclusions] using hc

theorem certificateEquivalence : Comparators.GorbowProofChecker.CertificateEquivalence := by
  intro n raw
  constructor
  · rintro ⟨ls,hv⟩
    unfold verifies at hv
    cases hh : checkProof ls with
    | none => simp [hh] at hv
    | some history =>
      cases history with
      | nil => simp [hh] at hv
      | cons e es =>
        rcases e with ⟨m,out⟩
        have he : n=m ∧ raw=out := by simpa [hh] using hv
        obtain ⟨rfl,rfl⟩ := he
        have hs := historySoundness [] (by simp [SoundHistory]) ls _ hh
        exact hs (n,raw) (by simp)
  · rintro ⟨φ,rfl,⟨p⟩⟩
    refine ⟨proofLines p,?_⟩
    have hr := compilationCorrectness n φ p []
    have hh := (compilationShape n φ p).2
    simp only [List.append_nil] at hr
    unfold verifies checkProof
    rw [hr]
    cases he : lineConclusions (proofLines p) with
    | nil => simp [he] at hh
    | cons e es =>
      have hx : e = (n,GorbowFormulaPrefixCode.encode φ) := by simpa [he] using hh
      simp [hx]

private theorem pr_context : Primrec context := Primrec.fst
private theorem pr_conclusion : Primrec conclusion := Primrec.fst.comp Primrec.snd
private theorem pr_rule : Primrec rule := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem pr_payload : Primrec payload := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
private theorem pr_tag : Primrec (fun l : Line => (payload l).1) := Primrec.fst.comp pr_payload
private theorem pr_args : Primrec (fun l : Line => (payload l).2.1) := Primrec.fst.comp (Primrec.snd.comp pr_payload)
private theorem pr_ref1 : Primrec (fun l : Line => (payload l).2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp pr_payload))
private theorem pr_ref2 : Primrec (fun l : Line => (payload l).2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pr_payload))
private theorem pr_annotation : Primrec (fun l : Line => ((payload l).1,(payload l).2.1)) := pr_tag.pair pr_args

private theorem pr_axiom (c : Nat → GorbowLogicalAxiomCode.Annotation → Option (List Nat))
    (hc : Primrec (fun p : Nat × GorbowLogicalAxiomCode.Annotation => c p.1 p.2)) :
    Primrec (fun l : Line => decide ((payload l).2.2.1 = 0 ∧ (payload l).2.2.2 = 0 ∧
      c (context l) ((payload l).1,(payload l).2.1) = some (conclusion l))) :=
  ((Primrec.eq.comp pr_ref1 (Primrec.const 0)).and ((Primrec.eq.comp pr_ref2 (Primrec.const 0)).and
    (Primrec.eq.comp (hc.comp (pr_context.pair pr_annotation)) (Primrec.option_some.comp pr_conclusion)))).decide

private def mpLeaf (p : (Nat × List Nat) × Entry × Entry) : Bool :=
  decide (p.2.1.1 = p.1.1 ∧ p.2.2.1 = p.1.1 ∧ p.2.1.2 = binary 7 p.2.2.2 p.1.2)
private theorem pr_mpLeaf : Primrec mpLeaf := by
  have hn : Primrec (fun p : (Nat × List Nat) × Entry × Entry => p.1.1) := Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : (Nat × List Nat) × Entry × Entry => p.1.2) := Primrec.snd.comp Primrec.fst
  have ha : Primrec (fun p : (Nat × List Nat) × Entry × Entry => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : (Nat × List Nat) × Entry × Entry => p.2.2) := Primrec.snd.comp Primrec.snd
  exact ((Primrec.eq.comp (Primrec.fst.comp ha) hn).and
    ((Primrec.eq.comp (Primrec.fst.comp hb) hn).and (Primrec.eq.comp (Primrec.snd.comp ha)
      (GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp
        ((Primrec.const 7).pair ((Primrec.snd.comp hb).pair hr)))))).decide
private def mpOptions (p : (Nat × List Nat) × Option Entry × Option Entry) : Bool :=
  match p.2.1,p.2.2 with | some a,some b => mpLeaf (p.1,a,b) | _,_ => false
private theorem pr_mpOptions : Primrec mpOptions := by
  have inner : Primrec (fun p : ((Nat × List Nat) × Option Entry × Option Entry) × Entry =>
      (match p.1.2.2 with | none => false | some b => mpLeaf (p.1.1,p.2,b))) := by
    have leaf : Primrec (fun p : (((Nat × List Nat) × Option Entry × Option Entry) × Entry) × Entry =>
        mpLeaf (p.1.1.1,p.1.2,p.2)) :=
      pr_mpLeaf.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
    have h := Primrec.option_casesOn
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst) : Primrec (fun p : ((Nat × List Nat) × Option Entry × Option Entry) × Entry => p.1.2.2))
      (Primrec.const false) leaf.to₂
    exact h.of_eq (fun p => by cases hx : p.1.2.2 <;> simp [hx])
  have h := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd : Primrec (fun p : (Nat × List Nat) × Option Entry × Option Entry => p.2.1))
    (Primrec.const false) inner.to₂
  exact h.of_eq (fun p => by cases ha : p.2.1 <;> cases hb : p.2.2 <;> simp [mpOptions,ha,hb])
private theorem pr_mp : Primrec (fun p : History × Line =>
    if (payload p.2).1 = 0 ∧ (payload p.2).2.1 = [] then
      match p.1[(payload p.2).2.2.1]?, p.1[(payload p.2).2.2.2]? with
      | some a,some b => decide (a.1=context p.2 ∧ b.1=context p.2 ∧ a.2=binary 7 b.2 (conclusion p.2))
      | _,_ => false
    else false) := by
  have hg : PrimrecPred (fun p : History × Line => (payload p.2).1 = 0 ∧ (payload p.2).2.1 = []) := (Primrec.eq.comp (pr_tag.comp Primrec.snd) (Primrec.const 0)).and
    (Primrec.eq.comp (pr_args.comp Primrec.snd) (Primrec.const []))
  have ha := Primrec.list_getElem?.comp (Primrec.fst : Primrec (fun p : History × Line => p.1)) (pr_ref1.comp Primrec.snd)
  have hb := Primrec.list_getElem?.comp (Primrec.fst : Primrec (fun p : History × Line => p.1)) (pr_ref2.comp Primrec.snd)
  exact Primrec.ite hg (pr_mpOptions.comp (((pr_context.pair pr_conclusion).comp Primrec.snd).pair (ha.pair hb))) (Primrec.const false)

private def genLeaf (p : (Nat × List Nat) × Entry) : Bool :=
  decide (p.2.1=p.1.1+1 ∧ p.1.2=unary 10 p.2.2)
private theorem pr_genLeaf : Primrec genLeaf :=
  ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))).and
    (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (GorbowCodeConstructorsProof.uniformPrograms.2.1.comp
      ((Primrec.const 10).pair (Primrec.snd.comp Primrec.snd))))).decide
private theorem pr_gen : Primrec (fun p : History × Line =>
    if (payload p.2).1 = 0 ∧ (payload p.2).2.1=[] ∧ (payload p.2).2.2.2=0 then
      match p.1[(payload p.2).2.2.1]? with
      | some a => decide (a.1=context p.2+1 ∧ conclusion p.2=unary 10 a.2)
      | _ => false
    else false) := by
  have hg : PrimrecPred (fun p : History × Line => (payload p.2).1 = 0 ∧ (payload p.2).2.1 = [] ∧ (payload p.2).2.2.2 = 0) := (Primrec.eq.comp (pr_tag.comp Primrec.snd) (Primrec.const 0)).and
    ((Primrec.eq.comp (pr_args.comp Primrec.snd) (Primrec.const [])).and
      (Primrec.eq.comp (pr_ref2.comp Primrec.snd) (Primrec.const 0)))
  have ha := Primrec.list_getElem?.comp (Primrec.fst : Primrec (fun p : History × Line => p.1)) (pr_ref1.comp Primrec.snd)
  have hb : Primrec (fun p : (History × Line) × Entry => genLeaf ((context p.1.2,conclusion p.1.2),p.2)) :=
    pr_genLeaf.comp ((((pr_context.pair pr_conclusion).comp Primrec.snd).comp Primrec.fst).pair Primrec.snd)
  have ht := Primrec.option_casesOn ha (Primrec.const false) hb.to₂
  have hf := Primrec.ite hg ht (Primrec.const false)
  exact hf.of_eq (fun p => by cases hx : p.1[(payload p.2).2.2.1]? <;> simp [hx,genLeaf])

private theorem pr_ruleCheck : Primrec (fun p : History × Line => ruleCheck p.1 p.2) := by
  have ht (i : Nat) : PrimrecPred (fun p : History × Line => rule p.2=i) :=
    Primrec.eq.comp (pr_rule.comp Primrec.snd) (Primrec.const i)
  have h3 := Primrec.ite (ht 3) pr_gen (Primrec.const false)
  have h2 := Primrec.ite (ht 2) pr_mp h3
  have h1 := Primrec.ite (ht 1)
    ((pr_axiom GorbowArithmeticAxiomCode.compile GorbowArithmeticAxiomCodeProof.uniformProgram).comp Primrec.snd) h2
  exact Primrec.ite (ht 0)
    ((pr_axiom GorbowLogicalAxiomCode.compile GorbowLogicalAxiomCodeProof.uniformPrograms.2.2).comp Primrec.snd) h1
private theorem pr_lineCheck : Primrec (fun p : History × Line => lineCheck p.1 p.2) :=
  Primrec.and.comp
    (GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp ((pr_context.pair pr_conclusion).comp Primrec.snd)) pr_ruleCheck
private theorem pr_stepSome : Primrec (fun p : (Option History × Line) × History =>
    if lineCheck p.2 p.1.2 then some ((context p.1.2,conclusion p.1.2)::p.2) else none) := by
  have hl : Primrec (fun p : (Option History × Line) × History => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.ite (Primrec.eq.comp (pr_lineCheck.comp (Primrec.snd.pair hl)) (Primrec.const true))
    (Primrec.option_some.comp (Primrec.list_cons.comp ((pr_context.pair pr_conclusion).comp hl) Primrec.snd)) (Primrec.const none)
private theorem pr_step : Primrec (fun p : Option History × Line => step p.1 p.2) :=
  Primrec.option_bind Primrec.fst pr_stepSome.to₂
private theorem pr_run : Primrec (fun p : History × List Line => run p.1 p.2) := by
  have hs : Primrec (fun p : (History × List Line) × Option History × Line => step p.2.1 p.2.2) := pr_step.comp Primrec.snd
  exact Primrec.list_foldl Primrec.snd (Primrec.option_some.comp Primrec.fst) hs.to₂
private theorem pr_checkProof : Primrec checkProof := pr_run.comp ((Primrec.const []).pair Primrec.id)
private theorem pr_verifyHead : Primrec (fun p : (Nat × List Nat × List Line) × Entry × History =>
    decide (p.1.1=p.2.1.1 ∧ p.1.2.1=p.2.1.2)) :=
  ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).decide
private theorem pr_verifyHistory : Primrec (fun p : (Nat × List Nat × List Line) × History =>
    (match p.2 with | [] => false | e::_ => decide (p.1.1=e.1 ∧ p.1.2.1=e.2))) := by
  have hh : Primrec (fun p : ((Nat × List Nat × List Line) × History) × Entry × History =>
      decide (p.1.1.1=p.2.1.1 ∧ p.1.1.2.1=p.2.1.2)) :=
    pr_verifyHead.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have h := Primrec.list_casesOn (Primrec.snd : Primrec (fun p : (Nat × List Nat × List Line) × History => p.2)) (Primrec.const false) hh.to₂
  exact h.of_eq (fun p => by cases hx : p.2 <;> simp [hx])
private theorem pr_verifies : Primrec (fun p : Nat × List Nat × List Line => verifies p.1 p.2.1 p.2.2) := by
  have h := Primrec.option_casesOn (pr_checkProof.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const false) pr_verifyHistory.to₂
  exact h.of_eq (fun p => by unfold verifies; cases checkProof p.2.2 with
    | none => rfl
    | some h => cases h <;> rfl)

theorem uniformPrograms : Comparators.GorbowProofChecker.UniformPrograms :=
  ⟨pr_ruleCheck,pr_lineCheck,pr_step,pr_run,pr_checkProof,pr_verifies⟩

theorem gorbowProofChecker : Comparators.GorbowProofChecker.Target :=
  ⟨referenceBounds,runConcatenation,historySoundness,compilationShape,compilationCorrectness,
    certificateEquivalence,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof

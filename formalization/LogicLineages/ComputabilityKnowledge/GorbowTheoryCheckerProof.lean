module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryChecker
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowTheoryProof
open GorbowProofChecker (Line Payload History Entry context conclusion rule payload logicalLine arithmeticLine mpLine generalizeLine lineConclusions)
open GorbowTheoryChecker

namespace Spec
def AxiomExact (axCheck : List Nat → Bool) : Prop := ∀ n raw p,
  GorbowTheoryChecker.axiomCheck axCheck n raw p=true ↔ ∃ σ : Sentence,
    p=(0,[GorbowFormulaPrefixCode.encode σ],0,0) ∧ ProgramTheory axCheck σ ∧
    raw=GorbowFormulaPrefixCode.encode (weakenClosed n σ)

def RuleDispatch (axCheck : List Nat → Bool) : Prop := ∀ history line,
  (rule line≠4 → GorbowTheoryChecker.ruleCheck axCheck history line=GorbowProofChecker.ruleCheck history line) ∧
  (rule line=4 → GorbowTheoryChecker.ruleCheck axCheck history line=axiomCheck axCheck (context line) (conclusion line) (payload line)) ∧
  (4<rule line → GorbowTheoryChecker.ruleCheck axCheck history line=false)

def ReferenceBounds (axCheck : List Nat → Bool) : Prop := ∀ history line, GorbowTheoryChecker.lineCheck axCheck history line=true →
  (rule line=2 → (payload line).2.2.1<history.length ∧ (payload line).2.2.2<history.length) ∧
  (rule line=3 → (payload line).2.2.1<history.length)

def RunConcatenation (axCheck : List Nat → Bool) : Prop := ∀ history a b,
  GorbowTheoryChecker.run axCheck history (a++b)=
    (GorbowTheoryChecker.run axCheck history a).bind (fun next => GorbowTheoryChecker.run axCheck next b)

def HistorySoundness (axCheck : List Nat → Bool) : Prop := ∀ history, GorbowTheoryChecker.SoundHistory axCheck history → ∀ lines next,
  GorbowTheoryChecker.run axCheck history lines=some next → GorbowTheoryChecker.SoundHistory axCheck next

def CompilationShape (axCheck : List Nat → Bool) : Prop := ∀ n (φ : Formula n) (p : Derivation (ProgramTheory axCheck) φ),
  0<(GorbowTheoryChecker.proofLines axCheck p).length ∧
  (lineConclusions (GorbowTheoryChecker.proofLines axCheck p)).head?=some (n,GorbowFormulaPrefixCode.encode φ)

def CompilationCorrectness (axCheck : List Nat → Bool) : Prop := ∀ n (φ : Formula n) (p : Derivation (ProgramTheory axCheck) φ) history,
  GorbowTheoryChecker.run axCheck history (GorbowTheoryChecker.proofLines axCheck p)=
    some (lineConclusions (GorbowTheoryChecker.proofLines axCheck p)++history)

def CertificateEquivalence (axCheck : List Nat → Bool) : Prop := ∀ n raw,
  (∃ lines, GorbowTheoryChecker.verifies axCheck n raw lines=true) ↔
  ∃ φ : Formula n, raw=GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Derivation (ProgramTheory axCheck) φ)

def MalformedRejection (axCheck : List Nat → Bool) : Prop := ∀ n raw,
  GorbowSyntaxValidation.validFormula n raw=false → ∀ lines, GorbowTheoryChecker.verifies axCheck n raw lines=false

def UniformPrograms (axCheck : List Nat → Bool) : Prop := Primrec axCheck →
  Primrec (fun p : Nat × List Nat × Payload => axiomCheck axCheck p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : History × Line => GorbowTheoryChecker.ruleCheck axCheck p.1 p.2) ∧
  Primrec (fun p : History × Line => GorbowTheoryChecker.lineCheck axCheck p.1 p.2) ∧
  Primrec (fun p : Option History × Line => GorbowTheoryChecker.step axCheck p.1 p.2) ∧
  Primrec (fun p : History × List Line => GorbowTheoryChecker.run axCheck p.1 p.2) ∧
  Primrec (GorbowTheoryChecker.checkProof axCheck) ∧
  Primrec (fun p : Nat × List Nat × List Line => GorbowTheoryChecker.verifies axCheck p.1 p.2.1 p.2.2)

end Spec

private theorem validEncode {n : Nat} (φ : Formula n) :
    GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode φ)=true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mpr
    ⟨φ,(GorbowFormulaPrefixCodeProof.decoderExact _ _ φ).mpr rfl⟩
private theorem weakenCode (n : Nat) (σ : Sentence) :
    GorbowSubstitutionCode.substituteFormulaCode 0 n [] (GorbowFormulaPrefixCode.encode σ)=
      some (GorbowFormulaPrefixCode.encode (weakenClosed n σ)) := by
  apply (GorbowSubstitutionCodeProof.exactOutput.2 0 n _ _ _).mpr
  exact ⟨Fin.elim0,σ,by simp [GorbowLiftedDictionary.dictionary],rfl,rfl⟩

theorem axiomExact (axCheck : List Nat → Bool) : Spec.AxiomExact axCheck := by
  intro n raw p
  constructor
  · intro h
    rcases p with ⟨tag,args,r1,r2⟩
    have hh : tag=0 ∧ args.length=1 ∧ r1=0 ∧ r2=0 ∧
        GorbowSyntaxValidation.validFormula 0 (args.getD 0 [])=true ∧
        axCheck (args.getD 0 [])=true ∧
        GorbowSubstitutionCode.substituteFormulaCode 0 n [] (args.getD 0 [])=some raw := by
      simpa only [axiomCheck,decide_eq_true_eq] using h
    obtain ⟨rfl,hlen,rfl,rfl,hv,ha,hs⟩ := hh
    obtain ⟨araw,rfl⟩ := List.length_eq_one_iff.mp hlen
    simp only [List.getD_cons_zero] at hv ha hs
    obtain ⟨σ,hσ⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 0 araw).mp hv
    have he := (GorbowFormulaPrefixCodeProof.decoderExact 0 araw σ).mp hσ
    subst araw
    have hw := weakenCode n σ
    exact ⟨σ,rfl,ha,(Option.some.inj (hs.symm.trans hw))⟩
  · rintro ⟨σ,rfl,ha,rfl⟩
    simpa [axiomCheck,validEncode,weakenCode,ProgramTheory] using ha

theorem ruleDispatch (axCheck : List Nat → Bool) : Spec.RuleDispatch axCheck := by
  intro h l
  refine ⟨fun h4 => by simp [ruleCheck,h4],fun h4 => by simp [ruleCheck,h4],?_⟩
  intro hr
  have h0 : rule l≠0 := by omega
  have h1 : rule l≠1 := by omega
  have h2 : rule l≠2 := by omega
  have h3 : rule l≠3 := by omega
  have h4 : rule l≠4 := by omega
  simp [ruleCheck,h4,GorbowProofChecker.ruleCheck,h0,h1,h2,h3]
private theorem lineParts (axCheck : List Nat → Bool) {h : History} {l : Line} (hc : (lineCheck axCheck) h l = true) :
    GorbowSyntaxValidation.validFormula (context l) (conclusion l) = true ∧ (ruleCheck axCheck) h l = true := by
  simpa [lineCheck] using hc

private theorem mpInfo {h : History} {l : Line} (hc : GorbowProofChecker.ruleCheck h l = true) (hr : rule l = 2) :
    ∃ a b, h[(payload l).2.2.1]? = some a ∧ h[(payload l).2.2.2]? = some b ∧
      a.1 = context l ∧ b.1 = context l ∧ a.2 = binary 7 b.2 (conclusion l) := by
  simp only [GorbowProofChecker.ruleCheck,hr,show (2:Nat) ≠ 0 by omega,show (2:Nat) ≠ 1 by omega,if_false,if_true] at hc
  split at hc
  · cases ha : h[(payload l).2.2.1]? with
    | none => simp [ha] at hc
    | some a =>
      cases hb : h[(payload l).2.2.2]? with
      | none => simp [ha,hb] at hc
      | some b => exact ⟨a,b,rfl,rfl,by simpa [ha,hb] using hc⟩
  · simp at hc

private theorem genInfo {h : History} {l : Line} (hc : GorbowProofChecker.ruleCheck h l = true) (hr : rule l = 3) :
    ∃ a, h[(payload l).2.2.1]? = some a ∧ a.1 = context l+1 ∧ conclusion l = unary 10 a.2 := by
  simp only [GorbowProofChecker.ruleCheck,hr,show (3:Nat) ≠ 0 by omega,show (3:Nat) ≠ 1 by omega,
    show (3:Nat) ≠ 2 by omega,if_false,if_true] at hc
  split at hc
  · cases ha : h[(payload l).2.2.1]? with
    | none => simp [ha] at hc
    | some a => exact ⟨a,rfl,by simpa [ha] using hc⟩
  · simp at hc

theorem referenceBounds (axCheck : List Nat → Bool) : Spec.ReferenceBounds axCheck := by
  intro h l hc
  obtain ⟨hv,hr⟩ := (lineParts axCheck) hc
  constructor
  · intro h2
    have h4 : rule l≠4 := by omega
    have ho : GorbowProofChecker.lineCheck h l=true := by
      simpa [GorbowProofChecker.lineCheck,ruleCheck,h4,hv] using hr
    exact (GorbowProofCheckerProof.referenceBounds h l ho).1 h2
  · intro h3
    have h4 : rule l≠4 := by omega
    have ho : GorbowProofChecker.lineCheck h l=true := by
      simpa [GorbowProofChecker.lineCheck,ruleCheck,h4,hv] using hr
    exact (GorbowProofCheckerProof.referenceBounds h l ho).2 h3

private theorem foldNone (axCheck : List Nat → Bool) (ls : List Line) : ls.foldl (step axCheck) none = none := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simpa [List.foldl,step] using ih

theorem runConcatenation (axCheck : List Nat → Bool) : Spec.RunConcatenation axCheck := by
  intro h a b
  simp only [run,List.foldl_append]
  cases a.foldl (step axCheck) (some h) <;> simp [(foldNone axCheck)]

private theorem runAppend (axCheck : List Nat → Bool) (h : History) (a b : List Line) :
    (run axCheck) h (a++b) = ((run axCheck) h a).bind (fun next => (run axCheck) next b) := (runConcatenation axCheck) h a b

private theorem lineSound (axCheck : List Nat → Bool) {h : History} (hs : (SoundHistory axCheck) h) (l : Line) (hc : (lineCheck axCheck) h l = true) :
    ∃ φ : Formula (context l), conclusion l = GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Derivation (ProgramTheory axCheck) φ) := by
  obtain ⟨hv,hr⟩ := (lineParts axCheck) hc
  obtain ⟨φ,hφ⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mp hv
  have he : conclusion l = GorbowFormulaPrefixCode.encode φ :=
    (GorbowFormulaPrefixCodeProof.decoderExact _ _ φ).mp hφ
  by_cases h4 : rule l=4
  · have hx : axiomCheck axCheck (context l) (conclusion l) (payload l)=true := by
      simpa [ruleCheck,h4] using hr
    obtain ⟨σ,_,hσ,heσ⟩ := (axiomExact axCheck _ _ _).mp hx
    exact ⟨weakenClosed (context l) σ,heσ,⟨.axiom σ hσ⟩⟩
  have hr : GorbowProofChecker.ruleCheck h l=true := by simpa [ruleCheck,h4] using hr
  by_cases h0 : rule l = 0
  · have hh : (payload l).2.2.1 = 0 ∧ (payload l).2.2.2 = 0 ∧
        GorbowLogicalAxiomCode.compile (context l) ((payload l).1,(payload l).2.1) = some (conclusion l) := by
      simpa [GorbowProofChecker.ruleCheck,h0] using hr
    obtain ⟨w,_,hw⟩ := (GorbowLogicalAxiomCodeProof.exactCompilation _ _ _).mp hh.2.2
    exact ⟨logicalFormula w,hw,⟨.logical w⟩⟩
  by_cases h1 : rule l = 1
  · have hh : (payload l).2.2.1 = 0 ∧ (payload l).2.2.2 = 0 ∧
        GorbowArithmeticAxiomCode.compile (context l) ((payload l).1,(payload l).2.1) = some (conclusion l) := by
      simpa [GorbowProofChecker.ruleCheck,h0,h1] using hr
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
  simp [GorbowProofChecker.ruleCheck,h0,h1,h2,h3] at hr

theorem historySoundness (axCheck : List Nat → Bool) : Spec.HistorySoundness axCheck := by
  intro h hs ls
  induction ls generalizing h with
  | nil => intro next hn; cases hn; exact hs
  | cons l ls ih =>
    intro next hn
    by_cases hc : (lineCheck axCheck) h l = true
    · have hnew : (SoundHistory axCheck) ((context l,conclusion l)::h) := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact (lineSound axCheck) hs l hc
        · exact hs e he
      apply ih _ hnew next
      simpa [run,List.foldl,step,hc] using hn
    · simp [run,List.foldl,step,hc,(foldNone axCheck)] at hn

private theorem logicalChecked (axCheck : List Nat → Bool) {n : Nat} (w : LogicalInstance n) (h : History) :
    (lineCheck axCheck) h (logicalLine w) = true := by
  have hw := (GorbowLogicalAxiomCodeProof.exactCompilation n _ _).mpr ⟨w,rfl,rfl⟩
  simpa [lineCheck,GorbowProofChecker.ruleCheck,logicalLine,context,conclusion,ruleCheck,rule,payload,validEncode] using hw
private theorem arithmeticChecked (axCheck : List Nat → Bool) {n : Nat} (w : ArithmeticInstance n) (h : History) :
    (lineCheck axCheck) h (arithmeticLine w) = true := by
  have hw := (GorbowArithmeticAxiomCodeProof.exactCompilation n _ _).mpr ⟨w,rfl,rfl⟩
  simpa [lineCheck,GorbowProofChecker.ruleCheck,arithmeticLine,context,conclusion,ruleCheck,rule,payload,validEncode] using hw

private theorem axiomChecked (axCheck : List Nat → Bool) (n : Nat) (σ : Sentence) (hσ : ProgramTheory axCheck σ) (h : History) :
    (lineCheck axCheck) h (axiomLine n σ)=true := by
  have ha := (axiomExact axCheck n _ _).mpr ⟨σ,rfl,hσ,rfl⟩
  simpa [lineCheck,ruleCheck,axiomLine,context,conclusion,rule,payload,validEncode] using ha

private theorem conclusionLength (ls : List Line) : (lineConclusions ls).length = ls.length := by
  simp [lineConclusions]

theorem compilationShape (axCheck : List Nat → Bool) : Spec.CompilationShape axCheck := by
  intro n φ p
  cases p <;> simp [proofLines,lineConclusions,logicalLine,arithmeticLine,axiomLine,mpLine,generalizeLine,
    context,conclusion,List.reverse_append,List.map_append,List.length_append]

private theorem getZeroAppend {xs ys : History} {e : Entry} (h : xs.head? = some e) :
    (xs++ys)[0]? = some e := by
  cases xs <;> simp_all
private theorem getLengthAppend {xs ys zs : History} {e : Entry} (h : ys.head? = some e) :
    (xs++ys++zs)[xs.length]? = some e := by
  induction xs with
  | nil => simpa using getZeroAppend (ys := zs) h
  | cons a xs ih => simpa using ih

theorem compilationCorrectness (axCheck : List Nat → Bool) : Spec.CompilationCorrectness axCheck := by
  intro n φ p
  induction p with
  | logical w =>
    intro h
    simp [proofLines,run,step,(logicalChecked axCheck),lineConclusions]
  | arithmetic w =>
    intro h
    simp [proofLines,run,step,(arithmeticChecked axCheck),lineConclusions]
  | «axiom» σ hσ =>
    intro h
    simp [proofLines,run,step,(axiomChecked axCheck),hσ,lineConclusions]
  | @mp n a b p q ihp ihq =>
    intro h
    let hp := lineConclusions ((proofLines axCheck) p)
    let hq := lineConclusions ((proofLines axCheck) q)
    have ep : (hq++hp++h)[((proofLines axCheck) q).length]? = some (n,GorbowFormulaPrefixCode.encode (.imp a b)) := by
      rw [← conclusionLength (proofLines axCheck q)]
      exact getLengthAppend ((compilationShape axCheck) _ _ p).2
    have eq : (hq++hp++h)[0]? = some (n,GorbowFormulaPrefixCode.encode a) := by
      simpa [List.append_assoc] using getZeroAppend (ys := hp++h) ((compilationShape axCheck) _ _ q).2
    simp only [List.append_assoc] at ep eq
    have hc : (lineCheck axCheck) (hq++hp++h) (mpLine n (GorbowFormulaPrefixCode.encode b) ((proofLines axCheck) q).length 0) = true := by
      simp [lineCheck,GorbowProofChecker.ruleCheck,mpLine,context,conclusion,ruleCheck,rule,payload,validEncode,ep,eq,
        GorbowFormulaPrefixCode.encode,binary]
    rw [proofLines,(runAppend axCheck),(runAppend axCheck),ihp]
    simp only [Option.bind_some]
    rw [ihq]
    simp only [Option.bind_some]
    have hc' : (lineCheck axCheck) (hq++(hp++h)) (mpLine n (GorbowFormulaPrefixCode.encode b) ((proofLines axCheck) q).length 0) = true := by
      simpa only [List.append_assoc] using hc
    change (run axCheck) (hq++(hp++h)) [_] = _
    simp only [run,List.foldl,step,Option.bind_some,hc',if_true]
    congr 1
    simp [lineConclusions,List.reverse_append,List.map_append,List.append_assoc,hp,hq]
    simpa [lineConclusions,hp,hq,List.append_assoc] using hc
  | @generalize n a p ih =>
    intro h
    have ep : (lineConclusions ((proofLines axCheck) p)++h)[0]? = some (n+1,GorbowFormulaPrefixCode.encode a) :=
      getZeroAppend ((compilationShape axCheck) _ _ p).2
    have hc : (lineCheck axCheck) (lineConclusions ((proofLines axCheck) p)++h)
        (generalizeLine n (GorbowFormulaPrefixCode.encode (.all a)) 0) = true := by
      change (GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode (.all a)) && _) = true
      rw [validEncode]
      simp [ruleCheck,GorbowProofChecker.ruleCheck,generalizeLine,context,conclusion,rule,payload,ep,GorbowFormulaPrefixCode.encode,unary]
    rw [proofLines,(runAppend axCheck),ih]
    simp only [Option.bind_some]
    simp only [run,List.foldl,step,Option.bind_some,hc,if_true]
    congr 1
    simp [lineConclusions,List.reverse_append,List.map_append,List.append_assoc]
    simpa [lineConclusions] using hc

theorem certificateEquivalence (axCheck : List Nat → Bool) : Spec.CertificateEquivalence axCheck := by
  intro n raw
  constructor
  · rintro ⟨ls,hv⟩
    unfold verifies at hv
    cases hh : (checkProof axCheck) ls with
    | none => simp [hh] at hv
    | some history =>
      cases history with
      | nil => simp [hh] at hv
      | cons e es =>
        rcases e with ⟨m,out⟩
        have he : n=m ∧ raw=out := by simpa [hh] using hv
        obtain ⟨rfl,rfl⟩ := he
        have hs := (historySoundness axCheck) [] (by simp [SoundHistory]) ls _ hh
        exact hs (n,raw) (by simp)
  · rintro ⟨φ,rfl,⟨p⟩⟩
    refine ⟨(proofLines axCheck) p,?_⟩
    have hr := (compilationCorrectness axCheck) n φ p []
    have hh := ((compilationShape axCheck) n φ p).2
    simp only [List.append_nil] at hr
    unfold verifies checkProof
    rw [hr]
    cases he : lineConclusions ((proofLines axCheck) p) with
    | nil => simp [he] at hh
    | cons e es =>
      have hx : e = (n,GorbowFormulaPrefixCode.encode φ) := by simpa [he] using hh
      simp [hx]


theorem malformedRejection (axCheck : List Nat → Bool) : Spec.MalformedRejection axCheck := by
  intro n raw hbad lines
  cases hv : verifies axCheck n raw lines with
  | false => rfl
  | true =>
    obtain ⟨φ,he,_⟩ := (certificateEquivalence axCheck n raw).mp ⟨lines,hv⟩
    have hh := validEncode φ
    rw [←he,hbad] at hh
    contradiction

private theorem pr_context : Primrec context := Primrec.fst
private theorem pr_conclusion : Primrec conclusion := Primrec.fst.comp Primrec.snd
private theorem pr_rule : Primrec rule := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem pr_payload : Primrec payload := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
private abbrev AInput := Nat × List Nat × Payload
private theorem pr_n : Primrec (fun p : AInput => p.1) := Primrec.fst
private theorem pr_raw : Primrec (fun p : AInput => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem pr_p : Primrec (fun p : AInput => p.2.2) := Primrec.snd.comp Primrec.snd
private theorem pr_tag : Primrec (fun p : AInput => p.2.2.1) := Primrec.fst.comp pr_p
private theorem pr_args : Primrec (fun p : AInput => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp pr_p)
private theorem pr_ref1 : Primrec (fun p : AInput => p.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp pr_p))
private theorem pr_ref2 : Primrec (fun p : AInput => p.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pr_p))
private theorem pr_axiomRaw : Primrec (fun p : AInput => p.2.2.2.1.getD 0 []) :=
  (Primrec.list_getD ([] : List Nat)).comp pr_args (Primrec.const 0)
private theorem pr_weaken : Primrec (fun p : AInput =>
    GorbowSubstitutionCode.substituteFormulaCode 0 p.1 [] (p.2.2.2.1.getD 0 [])) :=
  GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.const 0).pair (pr_n.pair ((Primrec.const []).pair pr_axiomRaw)))
private theorem pr_axiomCheck (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : AInput => axiomCheck axCheck p.1 p.2.1 p.2.2) := by
  have hv := GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp ((Primrec.const 0).pair pr_axiomRaw)
  exact ((Primrec.eq.comp pr_tag (Primrec.const 0)).and
    ((Primrec.eq.comp (Primrec.list_length.comp pr_args) (Primrec.const 1)).and
    ((Primrec.eq.comp pr_ref1 (Primrec.const 0)).and
    ((Primrec.eq.comp pr_ref2 (Primrec.const 0)).and
    ((Primrec.eq.comp hv (Primrec.const true)).and
    ((Primrec.eq.comp (ha.comp pr_axiomRaw) (Primrec.const true)).and
      (Primrec.eq.comp pr_weaken (Primrec.option_some.comp pr_raw)))))))).decide
private theorem pr_ruleCheck (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : History × Line => ruleCheck axCheck p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp (pr_rule.comp Primrec.snd) (Primrec.const 4))
    ((pr_axiomCheck axCheck ha).comp ((pr_context.pair (pr_conclusion.pair pr_payload)).comp Primrec.snd))
    GorbowProofCheckerProof.uniformPrograms.1
private theorem pr_lineCheck (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : History × Line => lineCheck axCheck p.1 p.2) :=
  Primrec.and.comp
    (GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp ((pr_context.pair pr_conclusion).comp Primrec.snd))
    (pr_ruleCheck axCheck ha)
private theorem pr_stepSome (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : (Option History × Line) × History =>
      if lineCheck axCheck p.2 p.1.2 then some ((context p.1.2,conclusion p.1.2)::p.2) else none) := by
  have hl : Primrec (fun p : (Option History × Line) × History => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.ite (Primrec.eq.comp ((pr_lineCheck axCheck ha).comp (Primrec.snd.pair hl)) (Primrec.const true))
    (Primrec.option_some.comp (Primrec.list_cons.comp ((pr_context.pair pr_conclusion).comp hl) Primrec.snd)) (Primrec.const none)
private theorem pr_step (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : Option History × Line => step axCheck p.1 p.2) :=
  Primrec.option_bind Primrec.fst (pr_stepSome axCheck ha).to₂
private theorem pr_run (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : History × List Line => run axCheck p.1 p.2) := by
  have hs : Primrec (fun p : (History × List Line) × Option History × Line => step axCheck p.2.1 p.2.2) :=
    (pr_step axCheck ha).comp Primrec.snd
  exact Primrec.list_foldl Primrec.snd (Primrec.option_some.comp Primrec.fst) hs.to₂
private theorem pr_checkProof (axCheck : List Nat → Bool) (ha : Primrec axCheck) : Primrec (checkProof axCheck) :=
  (pr_run axCheck ha).comp ((Primrec.const []).pair Primrec.id)
private theorem pr_verifyHead : Primrec (fun p : (Nat × List Nat × List Line) × Entry × History =>
    decide (p.1.1=p.2.1.1 ∧ p.1.2.1=p.2.1.2)) :=
  ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).decide
private theorem pr_verifyHistory : Primrec (fun p : (Nat × List Nat × List Line) × History =>
    match p.2 with | [] => false | (m,out)::_ => decide (p.1.1=m ∧ p.1.2.1=out)) := by
  have h := Primrec.list_casesOn Primrec.snd (Primrec.const false)
    (pr_verifyHead.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact h.of_eq (fun p => by cases p.2 <;> rfl)
private theorem pr_verifies (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun p : Nat × List Nat × List Line => verifies axCheck p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × List Nat × List Line => checkProof axCheck p.2.2) :=
    (pr_checkProof axCheck ha).comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.option_casesOn hc (Primrec.const false) pr_verifyHistory.to₂
  apply h.of_eq
  intro p
  cases hh : checkProof axCheck p.2.2 with
  | none => simp [verifies,hh]
  | some history => cases history <;> simp [verifies,hh]

theorem uniformPrograms (axCheck : List Nat → Bool) : Spec.UniformPrograms axCheck := by
  intro ha
  exact ⟨pr_axiomCheck axCheck ha,pr_ruleCheck axCheck ha,pr_lineCheck axCheck ha,
    pr_step axCheck ha,pr_run axCheck ha,pr_checkProof axCheck ha,pr_verifies axCheck ha⟩

theorem gorbowTheoryChecker : Comparators.GorbowTheoryChecker.Target :=
  ⟨axiomExact,ruleDispatch,referenceBounds,runConcatenation,historySoundness,
    compilationShape,compilationCorrectness,certificateEquivalence,malformedRejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof

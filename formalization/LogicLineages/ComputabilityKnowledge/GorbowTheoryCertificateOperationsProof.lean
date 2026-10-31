module
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsProof
open GorbowSyntax GorbowProofChecker GorbowTheoryCertificateOperations GorbowTheoryCertificateOperationsTargets
open GorbowSortedSyntaxCode
open GorbowNumericCertificate (decodeCertificate certificateNumber)

private theorem line_suffix (ax : List Nat → Bool) (h tail : History) (l : Line)
    (hc : GorbowTheoryChecker.lineCheck ax h l = true) :
    GorbowTheoryChecker.lineCheck ax (h++tail) l = true := by
  have hparts : GorbowSyntaxValidation.validFormula (context l) (conclusion l)=true ∧
      GorbowTheoryChecker.ruleCheck ax h l=true := by simpa [GorbowTheoryChecker.lineCheck] using hc
  simp only [GorbowTheoryChecker.lineCheck,hparts.1,Bool.true_and]
  have hr := hparts.2
  by_cases h4 : rule l=4
  · simpa only [GorbowTheoryChecker.ruleCheck,h4,if_true] using hr
  simp only [GorbowTheoryChecker.ruleCheck,h4,if_false] at hr ⊢
  by_cases h2 : rule l=2
  · have hb := (GorbowTheoryCheckerProof.referenceBounds ax h l hc).1 h2
    have e1 := List.getElem?_append_left (l₂ := tail) hb.1
    have e2 := List.getElem?_append_left (l₂ := tail) hb.2
    simpa only [GorbowProofChecker.ruleCheck,h2,show (2:Nat)≠0 by omega,
      show (2:Nat)≠1 by omega,if_false,if_true,e1,e2] using hr
  by_cases h3 : rule l=3
  · have hb := (GorbowTheoryCheckerProof.referenceBounds ax h l hc).2 h3
    have e1 := List.getElem?_append_left (l₂ := tail) hb
    simpa only [GorbowProofChecker.ruleCheck,h3,show (3:Nat)≠0 by omega,
      show (3:Nat)≠1 by omega,show (3:Nat)≠2 by omega,if_false,if_true,e1] using hr
  simpa only [GorbowProofChecker.ruleCheck,h2,h3,if_false] using hr

private theorem fold_none (ax : List Nat → Bool) (ls : List Line) :
    ls.foldl (GorbowTheoryChecker.step ax) none = none := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simpa [List.foldl,GorbowTheoryChecker.step] using ih

theorem successfulHistoryExtension : SuccessfulHistoryExtension := by
  intro ax h ls
  induction ls generalizing h with
  | nil => intro out tail he; cases he; rfl
  | cons l ls ih =>
      intro out tail he
      by_cases hc : GorbowTheoryChecker.lineCheck ax h l=true
      · have he' : GorbowTheoryChecker.run ax ((context l,conclusion l)::h) ls=some out := by
          simpa [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hc] using he
        have hi := ih _ out tail he'
        simpa [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,line_suffix ax h tail l hc] using hi
      · simp [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hc,fold_none] at he

private theorem run_shape (ax : List Nat → Bool) (h : History) (ls : List Line) (out : History)
    (he : GorbowTheoryChecker.run ax h ls=some out) : out=lineConclusions ls++h := by
  induction ls generalizing h with
  | nil => simpa [GorbowTheoryChecker.run,lineConclusions] using he.symm
  | cons l ls ih =>
      by_cases hc : GorbowTheoryChecker.lineCheck ax h l=true
      · have he' : GorbowTheoryChecker.run ax ((context l,conclusion l)::h) ls=some out := by
          simpa [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hc] using he
        simpa [lineConclusions,List.reverse_cons,List.map_append,List.append_assoc] using ih _ he'
      · simp [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,hc,fold_none] at he

private theorem verify_info (ax : List Nat → Bool) (n : Nat) (raw : List Nat) (ls : List Line)
    (hv : GorbowTheoryChecker.verifies ax n raw ls=true) :
    ∃ h : History, GorbowTheoryChecker.run ax [] ls=some h ∧
      h.head?=some (n,raw) ∧ h.length=ls.length := by
  cases he : GorbowTheoryChecker.checkProof ax ls with
  | none => simp [GorbowTheoryChecker.verifies,he] at hv
  | some h =>
      cases h with
      | nil => simp [GorbowTheoryChecker.verifies,he] at hv
      | cons e tail =>
          have hpair : n=e.1 ∧ raw=e.2 := by simpa [GorbowTheoryChecker.verifies,he] using hv
          have hs := run_shape ax [] ls (e::tail) he
          refine ⟨e::tail,he,?_,?_⟩
          · cases e with
            | mk en er =>
              rcases hpair with ⟨rfl,rfl⟩
              rfl
          · simpa [lineConclusions] using congrArg List.length hs

private theorem valid_encode {n : Nat} (a : Formula n) :
    GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode a)=true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mpr
    ⟨a,(GorbowFormulaPrefixCodeProof.decoderExact _ _ a).mpr rfl⟩

private theorem mp_raw (ax : List Nat → Bool) (n : Nat) (a b : Formula n) (ci ca : List Line)
    (hi : GorbowTheoryChecker.verifies ax n (GorbowFormulaPrefixCode.encode (.imp a b)) ci=true)
    (ha : GorbowTheoryChecker.verifies ax n (GorbowFormulaPrefixCode.encode a) ca=true) :
    GorbowTheoryChecker.verifies ax n (GorbowFormulaPrefixCode.encode b)
      (mpLines n (GorbowFormulaPrefixCode.encode b) ci ca)=true := by
  obtain ⟨ih,hri,hhi,hli⟩ := verify_info ax n _ ci hi
  obtain ⟨ah,hra,hha,hla⟩ := verify_info ax n _ ca ha
  have hral : GorbowTheoryChecker.run ax ih ca=some (ah++ih) := by
    simpa using successfulHistoryExtension ax [] ca ah ih hra
  have e1 : (ah++ih)[ca.length]?=some (n,GorbowFormulaPrefixCode.encode (.imp a b)) := by
    rw [← hla,List.getElem?_append_right (by omega),Nat.sub_self]
    simpa only [List.head?_eq_getElem?] using hhi
  have hpos : 0<ah.length := by
    cases ah with
    | nil => simp at hha
    | cons e es => exact Nat.zero_lt_succ _
  have e2 : (ah++ih)[0]?=some (n,GorbowFormulaPrefixCode.encode a) := by
    rw [List.getElem?_append_left hpos]
    simpa only [List.head?_eq_getElem?] using hha
  have hl : GorbowTheoryChecker.lineCheck ax (ah++ih)
      (mpLine n (GorbowFormulaPrefixCode.encode b) ca.length 0)=true := by
    simp [GorbowTheoryChecker.lineCheck,GorbowTheoryChecker.ruleCheck,GorbowProofChecker.ruleCheck,
      mpLine,context,conclusion,rule,payload,valid_encode,e1,e2,GorbowFormulaPrefixCode.encode,GorbowCodeConstructors.binary]
  have hr : GorbowTheoryChecker.run ax [] (mpLines n (GorbowFormulaPrefixCode.encode b) ci ca)=
      some ((n,GorbowFormulaPrefixCode.encode b)::(ah++ih)) := by
    rw [mpLines,GorbowTheoryCheckerProof.runConcatenation,GorbowTheoryCheckerProof.runConcatenation,hri]
    simp only [Option.bind_some]
    rw [hral]
    simp only [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,Bind.bind,Option.bind_some,hl,if_true]
    rfl
  simp [GorbowTheoryChecker.verifies,GorbowTheoryChecker.checkProof,hr]

private theorem gen_raw (ax : List Nat → Bool) (n : Nat) (a : Formula (n+1)) (c : List Line)
    (ha : GorbowTheoryChecker.verifies ax (n+1) (GorbowFormulaPrefixCode.encode a) c=true) :
    GorbowTheoryChecker.verifies ax n (GorbowFormulaPrefixCode.encode (.all a))
      (generalizeLines n (GorbowFormulaPrefixCode.encode (.all a)) c)=true := by
  obtain ⟨h,hr,hh,_⟩ := verify_info ax (n+1) _ c ha
  have hh0 : h[0]?=some (n+1,GorbowFormulaPrefixCode.encode a) := by
    simpa only [List.head?_eq_getElem?] using hh
  have hl : GorbowTheoryChecker.lineCheck ax h
      (generalizeLine n (GorbowFormulaPrefixCode.encode (.all a)) 0)=true := by
    change (GorbowSyntaxValidation.validFormula n (GorbowFormulaPrefixCode.encode (.all a)) && _)=true
    rw [valid_encode]
    simp [GorbowTheoryChecker.ruleCheck,GorbowProofChecker.ruleCheck,
      generalizeLine,context,conclusion,rule,payload,hh0,GorbowFormulaPrefixCode.encode,GorbowCodeConstructors.unary]
  have hout : GorbowTheoryChecker.run ax [] (generalizeLines n (GorbowFormulaPrefixCode.encode (.all a)) c)=
      some ((n,GorbowFormulaPrefixCode.encode (.all a))::h) := by
    rw [generalizeLines,GorbowTheoryCheckerProof.runConcatenation,hr]
    simp only [GorbowTheoryChecker.run,List.foldl,GorbowTheoryChecker.step,Bind.bind,Option.bind_some,hl,if_true]
    rfl
  simp [GorbowTheoryChecker.verifies,GorbowTheoryChecker.checkProof,hout]

private theorem decode_formula {n : Nat} (a : Formula n) :
    decodeFormulaRaw (formulaCode a)=some (GorbowFormulaPrefixCode.encode a) :=
  (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 _ _).mpr rfl

private theorem numeric_info (ax : List Nat → Bool) (n : Nat) (a : Formula n) (c : Nat)
    (hc : GorbowTheoryNumericCertificate.check ax n (formulaCode a) c=true) :
    ∃ ls : List Line, decodeCertificate c=some ls ∧
      GorbowTheoryChecker.verifies ax n (GorbowFormulaPrefixCode.encode a) ls=true := by
  cases hd : decodeCertificate c with
  | none => simp [GorbowTheoryNumericCertificate.check,decode_formula,hd] at hc
  | some ls => exact ⟨ls,rfl,by simpa [GorbowTheoryNumericCertificate.check,decode_formula,hd] using hc⟩

theorem numericModusPonens : NumericModusPonens := by
  intro ax n a b ci ca hi ha
  obtain ⟨li,hli,hvi⟩ := numeric_info ax n (.imp a b) ci hi
  obtain ⟨la,hla,hva⟩ := numeric_info ax n a ca ha
  simp only [mpCertificate,decode_formula,hli,hla,Option.getD_some]
  change GorbowTheoryNumericCertificate.check ax n (formulaRawNumber (GorbowFormulaPrefixCode.encode b))
    (certificateNumber (mpLines n (GorbowFormulaPrefixCode.encode b) li la))=true
  rw [GorbowTheoryNumericCertificateProof.calibration]
  exact mp_raw ax n a b li la hvi hva

theorem numericGeneralization : NumericGeneralization := by
  intro ax n a c hc
  obtain ⟨ls,hls,hvs⟩ := numeric_info ax (n+1) a c hc
  simp only [generalizeCertificate,decode_formula,hls,Option.getD_some]
  change GorbowTheoryNumericCertificate.check ax n (formulaRawNumber (GorbowFormulaPrefixCode.encode (.all a)))
    (certificateNumber (generalizeLines n (GorbowFormulaPrefixCode.encode (.all a)) ls))=true
  rw [GorbowTheoryNumericCertificateProof.calibration]
  exact gen_raw ax n a ls hvs

private theorem pr_raw : Primrec (fun n => (decodeFormulaRaw n).getD []) :=
  Primrec.option_getD.comp GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1 (Primrec.const [])
private theorem pr_lines : Primrec (fun n => (decodeCertificate n).getD []) :=
  Primrec.option_getD.comp GorbowNumericCertificateProof.uniformPrograms.2.1 (Primrec.const [])

private theorem pr_mpLine : Primrec (fun z : Nat × List Nat × Nat => mpLine z.1 z.2.1 z.2.2 0) :=
  Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair ((Primrec.const 2).pair
    ((Primrec.const 0).pair ((Primrec.const []).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const 0))))))
private theorem pr_genLine : Primrec (fun z : Nat × List Nat => generalizeLine z.1 z.2 0) :=
  Primrec.fst.pair (Primrec.snd.pair ((Primrec.const 3).pair
    ((Primrec.const 0).pair ((Primrec.const []).pair ((Primrec.const 0).pair (Primrec.const 0))))))

theorem effectiveModusPonens : EffectiveModusPonens := by
  have hn : Primrec (fun z : Nat × Nat × Nat × Nat => z.1) := Primrec.fst
  have hf : Primrec (fun z : Nat × Nat × Nat × Nat => (decodeFormulaRaw z.2.1).getD []) :=
    pr_raw.comp (Primrec.fst.comp Primrec.snd)
  have hi : Primrec (fun z : Nat × Nat × Nat × Nat => (decodeCertificate z.2.2.1).getD []) :=
    pr_lines.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have ha : Primrec (fun z : Nat × Nat × Nat × Nat => (decodeCertificate z.2.2.2).getD []) :=
    pr_lines.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.encode.comp (Primrec.list_concat.comp (Primrec.list_append.comp hi ha)
    (pr_mpLine.comp (hn.pair (hf.pair (Primrec.list_length.comp ha)))))

theorem effectiveGeneralization : EffectiveGeneralization := by
  have hn : Primrec (fun z : Nat × Nat × Nat => z.1) := Primrec.fst
  have hf : Primrec (fun z : Nat × Nat × Nat => (decodeFormulaRaw z.2.1).getD []) :=
    pr_raw.comp (Primrec.fst.comp Primrec.snd)
  have hc : Primrec (fun z : Nat × Nat × Nat => (decodeCertificate z.2.2).getD []) :=
    pr_lines.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.encode.comp (Primrec.list_concat.comp hc (pr_genLine.comp (hn.pair hf)))

end LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsProof

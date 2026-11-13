module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProgramsProof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowEnumeratedProvability
open GorbowProofChecker (Line Payload History Entry context conclusion rule payload)
open List.Vector

/- The uniform actual step reconstruction below follows the accepted source
GorbowEnumeratedProvabilityProof, retaining its runtime code/fuel parameters.
It constructs the supplier; it is not a new correctness premise. -/
private theorem pr_context : Primrec context := Primrec.fst
private theorem pr_conclusion : Primrec conclusion := Primrec.fst.comp Primrec.snd
private theorem pr_rule : Primrec rule := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem pr_payload : Primrec payload := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

private abbrev AInput := Nat × List Nat × Payload

private theorem pr_n : Primrec (fun p : AInput => p.1) := Primrec.fst
private theorem pr_raw : Primrec (fun p : AInput => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem pr_p : Primrec (fun p : AInput => p.2.2) := Primrec.snd.comp Primrec.snd
private theorem pr_tag : Primrec (fun p : AInput => p.2.2.1) := Primrec.fst.comp pr_p
private theorem pr_args : Primrec (fun p : AInput => p.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp pr_p)
private theorem pr_ref1 : Primrec (fun p : AInput => p.2.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp pr_p))
private theorem pr_ref2 : Primrec (fun p : AInput => p.2.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp pr_p))
private theorem pr_axiomRaw : Primrec (fun p : AInput => p.2.2.2.1.getD 0 []) :=
  (Primrec.list_getD ([] : List Nat)).comp pr_args (Primrec.const 0)
private theorem pr_weaken : Primrec (fun p : AInput =>
    GorbowSubstitutionCode.substituteFormulaCode 0 p.1 [] (p.2.2.2.1.getD 0 [])) :=
  GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.const 0).pair (pr_n.pair ((Primrec.const []).pair pr_axiomRaw)))
private theorem pr_validAxiom : Primrec (fun p : AInput =>
    GorbowSyntaxValidation.validFormula 0 (p.2.2.2.1.getD 0 [])) :=
  GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp ((Primrec.const 0).pair pr_axiomRaw)

/-! ### The actual checker, uniformly in `(code,fuel)` -/

private theorem pr_boundedAxiom : Primrec (fun x : Parameters × AInput =>
    axiomCheck x.1 (x.2.2.2.2.1.getD 0 [])) :=
  StagesProof.uniformAxiomChecker.comp (Primrec.fst.pair (pr_axiomRaw.comp Primrec.snd))

private theorem pr_axiomCheckU : Primrec (fun x : Parameters × AInput =>
    GorbowTheoryChecker.axiomCheck (axiomCheck x.1) x.2.1 x.2.2.1 x.2.2.2) :=
  ((Primrec.eq.comp (pr_tag.comp Primrec.snd) (Primrec.const 0)).and
    ((Primrec.eq.comp (Primrec.list_length.comp (pr_args.comp Primrec.snd)) (Primrec.const 1)).and
    ((Primrec.eq.comp (pr_ref1.comp Primrec.snd) (Primrec.const 0)).and
    ((Primrec.eq.comp (pr_ref2.comp Primrec.snd) (Primrec.const 0)).and
    ((Primrec.eq.comp (pr_validAxiom.comp Primrec.snd) (Primrec.const true)).and
    ((Primrec.eq.comp pr_boundedAxiom (Primrec.const true)).and
      (Primrec.eq.comp (pr_weaken.comp Primrec.snd)
        (Primrec.option_some.comp (pr_raw.comp Primrec.snd))))))))).decide

private theorem pr_ruleCheckU : Primrec (fun x : Parameters × (History × Line) =>
    GorbowTheoryChecker.ruleCheck (axiomCheck x.1) x.2.1 x.2.2) := by
  have hl : Primrec (fun x : Parameters × (History × Line) => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hax : Primrec (fun x : Parameters × (History × Line) =>
      GorbowTheoryChecker.axiomCheck (axiomCheck x.1)
        (context x.2.2) (conclusion x.2.2) (payload x.2.2)) :=
    pr_axiomCheckU.comp (Primrec.fst.pair ((pr_context.pair (pr_conclusion.pair pr_payload)).comp hl))
  have hold : Primrec (fun x : Parameters × (History × Line) =>
      GorbowProofChecker.ruleCheck x.2.1 x.2.2) :=
    GorbowProofCheckerProof.uniformPrograms.1.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (pr_rule.comp hl) (Primrec.const 4)) hax hold

private theorem pr_lineCheckU : Primrec (fun x : Parameters × (History × Line) =>
    GorbowTheoryChecker.lineCheck (axiomCheck x.1) x.2.1 x.2.2) := by
  have hv : Primrec (fun x : Parameters × (History × Line) =>
      GorbowSyntaxValidation.validFormula (context x.2.2) (conclusion x.2.2)) :=
    GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp
      ((pr_context.pair pr_conclusion).comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.and.comp hv pr_ruleCheckU

private theorem pr_stepSomeU : Primrec (fun y : (Parameters × (Option History × Line)) × History =>
    if GorbowTheoryChecker.lineCheck (axiomCheck y.1.1) y.2 y.1.2.2 then
      some ((context y.1.2.2, conclusion y.1.2.2) :: y.2) else none) := by
  have hp : Primrec (fun y : (Parameters × (Option History × Line)) × History => y.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hl : Primrec (fun y : (Parameters × (Option History × Line)) × History => y.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hc : Primrec (fun y : (Parameters × (Option History × Line)) × History =>
      GorbowTheoryChecker.lineCheck (axiomCheck y.1.1) y.2 y.1.2.2) :=
    pr_lineCheckU.comp (hp.pair (Primrec.snd.pair hl))
  exact Primrec.ite (Primrec.eq.comp hc (Primrec.const true))
    (Primrec.option_some.comp (Primrec.list_cons.comp ((pr_context.pair pr_conclusion).comp hl)
      Primrec.snd))
    (Primrec.const none)

private theorem pr_stepU : Primrec (fun x : Parameters × (Option History × Line) =>
    GorbowTheoryChecker.step (axiomCheck x.1) x.2.1 x.2.2) :=
  Primrec.option_bind (Primrec.fst.comp Primrec.snd) pr_stepSomeU.to₂


private theorem pr_decodedState : Primrec decodedState :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (none,[]))

private theorem pr_decodedLines : Primrec decodedLines :=
  Primrec.option_getD.comp GorbowNumericCertificateProof.uniformPrograms.2.1 (Primrec.const [])

private theorem pr_transition : Primrec (fun x : (Nat × Nat) × State =>
    transition x.1.1 x.1.2 x.2) := by
  have hp : Primrec (fun x : (Nat × Nat) × State =>
      ((Denumerable.ofNat Code x.1.1,x.1.2) : Parameters)) :=
    ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)
  have hn : Primrec (fun z : ((Nat × Nat) × State) × (Line × List Line) =>
      (GorbowTheoryChecker.step (axiomCheck (Denumerable.ofNat Code z.1.1.1,z.1.1.2))
        z.1.2.1 z.2.1,z.2.2)) :=
    (pr_stepU.comp ((hp.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.fst.comp Primrec.snd)))).pair (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_casesOn (Primrec.snd.comp Primrec.snd) Primrec.snd hn.to₂
  exact h.of_eq (fun x => by
    rcases x with ⟨⟨index,fuel⟩,state,lines⟩
    cases lines <;> rfl)

private theorem pr_kernelFunction : Primrec kernelFunction := by
  have h0 : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have h1 : Primrec (fun v : List.Vector Nat 3 => v.tail.head) :=
    Primrec.vector_head.comp Primrec.vector_tail
  have h2 : Primrec (fun v : List.Vector Nat 3 => v.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp Primrec.vector_tail)
  exact Primrec.encode.comp (pr_transition.comp ((h1.pair h2).pair (pr_decodedState.comp h0)))

private theorem pr_boundFunction : Primrec boundFunction :=
  Primrec.encode.comp (pr_decodedLines.comp Primrec.vector_head)

private theorem pr_initialFunction : Primrec initialFunction :=
  Primrec.encode.comp ((Primrec.const (some ([] : History))).pair
    (pr_decodedLines.comp Primrec.vector_head))

private def historyTest (n : Nat) (raw : List Nat) (history : History) : Bool :=
  match history with
  | [] => false
  | (m,out)::_ => decide (n=m ∧ raw=out)

private theorem pr_historyTest : Primrec (fun x : (Nat × List Nat) × History =>
    historyTest x.1.1 x.1.2 x.2) := by
  have hb : Primrec (fun z : ((Nat × List Nat) × History) × (Entry × History) =>
      decide (z.1.1.1=z.2.1.1 ∧ z.1.1.2=z.2.1.2)) :=
    ((Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).decide
  have h := Primrec.list_casesOn Primrec.snd (Primrec.const false) hb.to₂
  exact h.of_eq (fun x => by cases x.2 <;> rfl)

private def optionHistoryTest (n : Nat) (raw : List Nat) (state : Option History) : Bool :=
  match state with
  | none => false
  | some history => historyTest n raw history

private theorem pr_optionHistoryTest : Primrec (fun x : (Nat × List Nat) × Option History =>
    optionHistoryTest x.1.1 x.1.2 x.2) := by
  have h := Primrec.option_casesOn Primrec.snd (Primrec.const false)
    (pr_historyTest.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact h.of_eq (fun x => by
    rcases x with ⟨⟨n,raw⟩,state⟩
    cases state <;> rfl)

private theorem finishBoolean (state : State) (n formula cert : Nat) :
    finish state n formula cert =
      ((GorbowSortedSyntaxCode.decodeFormulaRaw formula).isSome &&
        ((GorbowNumericCertificate.decodeCertificate cert).isSome &&
          optionHistoryTest n ((GorbowSortedSyntaxCode.decodeFormulaRaw formula).getD []) state.1)) := by
  cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw formula <;>
    cases hc : GorbowNumericCertificate.decodeCertificate cert <;>
    cases hs : state.1 with
    | none => simp only [finish,hf,hc,hs,Option.isSome_none,Option.isSome_some,
        Option.getD_some,optionHistoryTest,Bool.false_and,Bool.true_and]
    | some history => cases history <;>
        simp only [finish,hf,hc,hs,Option.isSome_none,Option.isSome_some,
          Option.getD_some,optionHistoryTest,historyTest,Bool.false_and,Bool.true_and] <;> rfl

private theorem pr_finishFunction : Primrec finishFunction := by
  have h0 : Primrec (fun v : List.Vector Nat 4 => v.head) := Primrec.vector_head
  have hn : Primrec (fun v : List.Vector Nat 4 => v.tail.head) :=
    Primrec.vector_head.comp Primrec.vector_tail
  have hf : Primrec (fun v : List.Vector Nat 4 => v.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp Primrec.vector_tail)
  have hc : Primrec (fun v : List.Vector Nat 4 => v.tail.tail.tail.head) :=
    Primrec.vector_head.comp (Primrec.vector_tail.comp (Primrec.vector_tail.comp Primrec.vector_tail))
  have hd := GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1.comp hf
  have hdc := GorbowNumericCertificateProof.uniformPrograms.2.1.comp hc
  have hraw := Primrec.option_getD.comp hd (Primrec.const [])
  have hh := pr_optionHistoryTest.comp
    ((hn.pair hraw).pair (Primrec.fst.comp (pr_decodedState.comp h0)))
  have hbool := Primrec.and.comp (Primrec.option_isSome.comp hd)
    (Primrec.and.comp (Primrec.option_isSome.comp hdc) hh)
  have h := Primrec.ite (Primrec.eq.comp hbool (Primrec.const true))
    (Primrec.const 1) (Primrec.const 0)
  exact h.of_eq (fun v => by rw [finishFunction,finishBoolean])

theorem nativePrograms : Targets.NativePrograms := by
  obtain ⟨kernel,hk⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 kernelFunction pr_kernelFunction
  obtain ⟨bound,hb⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 1 boundFunction pr_boundFunction
  obtain ⟨initial,hi⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 1 initialFunction pr_initialFunction
  obtain ⟨finalizer,hz⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 4 finishFunction pr_finishFunction
  exact ⟨kernel,bound,initial,finalizer,hk,hb,hi,hz⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProgramsProof

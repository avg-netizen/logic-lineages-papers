module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.LeavesProof
open GorbowSyntax GorbowTheoryProof GorbowPRProgram GorbowEnumeratedProvability
open GorbowProofChecker (Line Payload History Entry context conclusion rule payload)
open List.Vector

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


private theorem pr_decodedLine : Primrec decodedLine :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const defaultLine)

private theorem pr_withRule (r : Nat) : Primrec (withRule r) :=
  pr_context.pair (pr_conclusion.pair ((Primrec.const r).pair pr_payload))

private theorem pr_truth : Primrec truth := by
  have h := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const true))
    (Primrec.const 1) (Primrec.const 0)
  exact h.of_eq (fun b => by cases b <;> rfl)

private theorem pr_validFunction : Primrec validFunction :=
  pr_truth.comp (GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp
    ((pr_context.pair pr_conclusion).comp (pr_decodedLine.comp Primrec.vector_head)))

private theorem pr_logicalFunction : Primrec logicalFunction :=
  pr_truth.comp (GorbowProofCheckerProof.uniformPrograms.1.comp
    ((Primrec.const ([] : History)).pair ((pr_withRule 0).comp (pr_decodedLine.comp Primrec.vector_head))))

private theorem pr_arithmeticFunction : Primrec arithmeticFunction :=
  pr_truth.comp (GorbowProofCheckerProof.uniformPrograms.1.comp
    ((Primrec.const ([] : History)).pair ((pr_withRule 1).comp (pr_decodedLine.comp Primrec.vector_head))))

private def axiomInput (v : List.Vector Nat 3) : Parameters × AInput :=
  ((Denumerable.ofNat Code v.head,v.tail.head),
    context (decodedLine v.tail.tail.head),conclusion (decodedLine v.tail.tail.head),payload (decodedLine v.tail.tail.head))

private theorem pr_axiomInput : Primrec axiomInput := by
  have hi : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have hf : Primrec (fun v : List.Vector Nat 3 => v.tail.head) := Primrec.vector_head.comp Primrec.vector_tail
  have hl : Primrec (fun v : List.Vector Nat 3 => decodedLine v.tail.tail.head) :=
    pr_decodedLine.comp (Primrec.vector_head.comp (Primrec.vector_tail.comp Primrec.vector_tail))
  have hp : Primrec (fun v : List.Vector Nat 3 => ((Denumerable.ofNat Code v.head,v.tail.head) : Parameters)) :=
    ((Primrec.ofNat Code).comp hi).pair hf
  exact hp.pair ((pr_context.pair (pr_conclusion.pair pr_payload)).comp hl)

private theorem pr_axiomBoolean : Primrec (fun v : List.Vector Nat 3 =>
    GorbowTheoryChecker.axiomCheck (axiomCheck (axiomInput v).1)
      (axiomInput v).2.1 (axiomInput v).2.2.1 (axiomInput v).2.2.2) :=
  pr_axiomCheckU.comp pr_axiomInput

private theorem pr_axiomFunction : Primrec axiomFunction :=
  pr_truth.comp pr_axiomBoolean

theorem constructLeaves : Targets.ConstructLeaves := by
  obtain ⟨valid,hv⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 1 validFunction pr_validFunction
  obtain ⟨logical,hl⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 1 logicalFunction pr_logicalFunction
  obtain ⟨arithmetic,ha⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 1 arithmeticFunction pr_arithmeticFunction
  obtain ⟨axiomProgram,hax⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 axiomFunction pr_axiomFunction
  exact ⟨valid,logical,arithmetic,axiomProgram,hv,hl,ha,hax⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.LeavesProof

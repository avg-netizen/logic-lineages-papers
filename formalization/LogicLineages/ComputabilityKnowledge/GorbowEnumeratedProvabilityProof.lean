module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityStagesProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof
public import LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section
/-! Parameter-uniform numeric proof checking. The actual Hilbert certificate
checker of `GorbowTheoryChecker` is re-verified primitive recursive with the
bounded axiom parameters `(code,fuel)` carried explicitly through the axiom
rule, rule dispatch, line check, option-state step, list fold, final history
test and the formula/certificate decoders. The four bounded-stage clauses are
the already paid `StagesProof` theorems. One fixed arity-5 program then
decodes the ordinary program index from its first argument. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.Proof
open GorbowSyntax GorbowTheoryProof
open GorbowProofChecker (Line Payload History Entry context conclusion rule payload)

/-! ### Typed projections for the axiom rule -/

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

private theorem pr_runU : Primrec (fun x : Parameters × (History × List Line) =>
    GorbowTheoryChecker.run (axiomCheck x.1) x.2.1 x.2.2) := by
  have hs : Primrec (fun z : (Parameters × (History × List Line)) × Option History × Line =>
      GorbowTheoryChecker.step (axiomCheck z.1.1) z.2.1 z.2.2) :=
    pr_stepU.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) hs.to₂

private theorem pr_checkProofU : Primrec (fun x : Parameters × List Line =>
    GorbowTheoryChecker.checkProof (axiomCheck x.1) x.2) :=
  pr_runU.comp (Primrec.fst.pair ((Primrec.const ([] : History)).pair Primrec.snd))

private theorem pr_verifyHead : Primrec (fun p : (Nat × List Nat × List Line) × Entry × History =>
    decide (p.1.1 = p.2.1.1 ∧ p.1.2.1 = p.2.1.2)) :=
  ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))).decide

private theorem pr_verifyHistory : Primrec (fun p : (Nat × List Nat × List Line) × History =>
    match p.2 with | [] => false | (m, out) :: _ => decide (p.1.1 = m ∧ p.1.2.1 = out)) := by
  have h := Primrec.list_casesOn Primrec.snd (Primrec.const false)
    (pr_verifyHead.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact h.of_eq (fun p => by cases p.2 <;> rfl)

private abbrev VerifyInput := Parameters × (Nat × List Nat × List Line)

private theorem pr_verifiesCheck : Primrec (fun x : VerifyInput =>
    GorbowTheoryChecker.checkProof (axiomCheck x.1) x.2.2.2) := by
  have hi : Primrec (fun x : VerifyInput => (x.1, x.2.2.2)) :=
    Primrec.fst.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h := pr_checkProofU.comp hi
  exact h.of_eq (fun _ => rfl)

private theorem pr_verifiesOutput : Primrec (fun z : VerifyInput × History =>
    match z.2 with | [] => false | (m, out) :: _ => decide (z.1.2.1 = m ∧ z.1.2.2.1 = out)) := by
  have hi : Primrec (fun z : VerifyInput × History => (z.1.2, z.2)) :=
    (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  have h := pr_verifyHistory.comp hi
  exact h.of_eq (fun _ => rfl)

private theorem pr_verifiesU : Primrec (fun x : VerifyInput =>
    GorbowTheoryChecker.verifies (axiomCheck x.1) x.2.1 x.2.2.1 x.2.2.2) := by
  have h := Primrec.option_casesOn pr_verifiesCheck (Primrec.const false) pr_verifiesOutput.to₂
  apply h.of_eq
  intro x
  cases hh : GorbowTheoryChecker.checkProof (axiomCheck x.1) x.2.2.2 with
  | none => simp [GorbowTheoryChecker.verifies, hh]
  | some history => cases history <;> simp [GorbowTheoryChecker.verifies, hh]

/-! ### The numeric certificate checker, uniformly in `(code,fuel)` -/

private abbrev InnerInput := (Parameters × (Nat × Nat × Nat)) × List Nat

private theorem pr_innerCertificate : Primrec (fun y : InnerInput =>
    GorbowNumericCertificate.decodeCertificate y.1.2.2.2) :=
  GorbowNumericCertificateProof.uniformPrograms.2.1.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

private theorem pr_innerLines : Primrec (fun z : InnerInput × List Line =>
    GorbowTheoryChecker.verifies (axiomCheck z.1.1.1) z.1.1.2.1 z.1.2 z.2) := by
  have hi : Primrec (fun z : InnerInput × List Line =>
      (z.1.1.1, z.1.1.2.1, z.1.2, z.2)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have h := pr_verifiesU.comp hi
  exact h.of_eq (fun _ => rfl)

private theorem pr_innerU : Primrec (fun y : InnerInput =>
    match GorbowNumericCertificate.decodeCertificate y.1.2.2.2 with
    | none => false
    | some ls => GorbowTheoryChecker.verifies (axiomCheck y.1.1) y.1.2.1 y.2 ls) := by
  have h := Primrec.option_casesOn pr_innerCertificate (Primrec.const false) pr_innerLines.to₂
  exact h.of_eq (fun y => by
    cases hx : GorbowNumericCertificate.decodeCertificate y.1.2.2.2 <;> simp [hx])

theorem uniformNumericChecker : GorbowEnumeratedProvability.Targets.UniformNumericChecker := by
  have hformula : Primrec (fun p : Parameters × Nat × Nat × Nat =>
      GorbowSortedSyntaxCode.decodeFormulaRaw p.2.2.1) :=
    GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have h := Primrec.option_casesOn hformula (Primrec.const false) pr_innerU.to₂
  exact h.of_eq (fun p => by
    cases hf : GorbowSortedSyntaxCode.decodeFormulaRaw p.2.2.1 <;>
      cases hc : GorbowNumericCertificate.decodeCertificate p.2.2.2 <;>
        simp [check, GorbowTheoryNumericCertificate.check, hf, hc])

/-! ### Exact acceptance over the c.e. theory -/

theorem exactNumericAcceptance : GorbowEnumeratedProvability.Targets.ExactNumericAcceptance := by
  intro c n formula
  constructor
  · rintro ⟨fuel, certificate, h⟩
    obtain ⟨phi, hphi, hd⟩ := (GorbowTheoryNumericCertificateProof.proofEquivalence
      (axiomCheck (c, fuel)) n formula).mp ⟨certificate, h⟩
    exact ⟨phi, hphi, (StagesProof.finiteProofStage c n phi).mpr ⟨fuel, hd⟩⟩
  · rintro ⟨phi, hphi, hd⟩
    obtain ⟨fuel, hb⟩ := (StagesProof.finiteProofStage c n phi).mp hd
    obtain ⟨certificate, h⟩ := (GorbowTheoryNumericCertificateProof.proofEquivalence
      (axiomCheck (c, fuel)) n formula).mpr ⟨phi, hphi, hb⟩
    exact ⟨fuel, certificate, h⟩

/-! ### One fixed arity-5 program -/

private theorem pr_universal : Primrec (fun v : List.Vector Nat 5 =>
    if check (Denumerable.ofNat Code v.head, v.tail.head) v.tail.tail.head
      v.tail.tail.tail.head v.tail.tail.tail.tail.head then 1 else 0) := by
  have h0 : Primrec (fun v : List.Vector Nat 5 => v.head) := Primrec.vector_head
  have t1 : Primrec (fun v : List.Vector Nat 5 => v.tail) := Primrec.vector_tail
  have t2 : Primrec (fun v : List.Vector Nat 5 => v.tail.tail) := Primrec.vector_tail.comp t1
  have t3 : Primrec (fun v : List.Vector Nat 5 => v.tail.tail.tail) := Primrec.vector_tail.comp t2
  have t4 : Primrec (fun v : List.Vector Nat 5 => v.tail.tail.tail.tail) :=
    Primrec.vector_tail.comp t3
  have h1 : Primrec (fun v : List.Vector Nat 5 => v.tail.head) := Primrec.vector_head.comp t1
  have h2 : Primrec (fun v : List.Vector Nat 5 => v.tail.tail.head) := Primrec.vector_head.comp t2
  have h3 : Primrec (fun v : List.Vector Nat 5 => v.tail.tail.tail.head) :=
    Primrec.vector_head.comp t3
  have h4 : Primrec (fun v : List.Vector Nat 5 => v.tail.tail.tail.tail.head) :=
    Primrec.vector_head.comp t4
  have hcode : Primrec (fun v : List.Vector Nat 5 => (Denumerable.ofNat Code v.head : Code)) :=
    (Primrec.ofNat Code).comp h0
  have hargs : Primrec (fun v : List.Vector Nat 5 =>
      (((Denumerable.ofNat Code v.head, v.tail.head) : Parameters),
        v.tail.tail.head, v.tail.tail.tail.head, v.tail.tail.tail.tail.head)) :=
    (hcode.pair h1).pair (h2.pair (h3.pair h4))
  have hchk : Primrec (fun v : List.Vector Nat 5 =>
      check (Denumerable.ofNat Code v.head, v.tail.head) v.tail.tail.head
        v.tail.tail.tail.head v.tail.tail.tail.tail.head) :=
    uniformNumericChecker.comp hargs
  exact Primrec.ite (Primrec.eq.comp hchk (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)

theorem fixedUniversalProgram : GorbowEnumeratedProvability.Targets.FixedUniversalProgram := by
  obtain ⟨q, hq⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 5 _ pr_universal
  refine ⟨q, fun c fuel n formula certificate => ?_⟩
  rw [hq (arguments c fuel n formula certificate)]
  show (if check (Denumerable.ofNat Code (Encodable.encode c), fuel) n formula certificate
    then 1 else 0) = _
  rw [Denumerable.ofNat_encode]

theorem fullTarget : GorbowEnumeratedProvability.Targets.Target :=
  ⟨StagesProof.uniformAxiomChecker, StagesProof.boundedMonotonicity, StagesProof.exactAxiomUnion,
    StagesProof.finiteProofStage, uniformNumericChecker, exactNumericAcceptance,
    fixedUniversalProgram⟩

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.Proof

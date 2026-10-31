module
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentPrimitiveProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerProof
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalInput
open ForwardTranslation OrdinalSyntax

private theorem optionPairPrim {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {a : α → Option β} {b : α → Option γ} (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => do let u ← a x; let v ← b x; pure (u,v)) := by
  apply Primrec.option_bind ha
  change Primrec (fun p : α × β => do let v ← b p.1; pure (p.2,v))
  have h : Primrec (fun p : α × β => (b p.1).map (p.2, ·)) :=
    Primrec.option_map (hb.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  apply h.of_eq
  intro p
  cases b p.1 <;> rfl

/-- Genuine computability of the original literal-source syntax pipeline. -/
theorem compileSyntaxPrimitiveRecursive : Primrec compileSyntax := by
  have hctx : Primrec (fun q : Query => List.replicate q.1 0) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.fst (β := Bool × Nat × Nat)))
      (Primrec.const 0).to₂
    exact h.of_eq (fun q => by simp)
  have ha : Primrec (fun q : Query => DefaultSourceAssignment.assignmentCode (List.replicate q.1 0) q.2.2.1) :=
    DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp
      (hctx.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hb : Primrec (fun q : Query => DefaultSourceAssignment.assignmentCode (List.replicate q.1 0) q.2.2.2) :=
    DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp
      (hctx.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hpairs := optionPairPrim ha hb
  have hc : Primrec (fun p : Query × (List Nat × List Nat) => do
      let ac ← compileVectorCode p.2.1
      let bc ← compileVectorCode p.2.2
      pure (p.1.2.1, ac, bc)) := by
    have hac : Primrec (fun p : Query × (List Nat × List Nat) => compileVectorCode p.2.1) :=
      ordinalSyntaxVectorCompilerPrimitiveRecursive.comp (Primrec.fst.comp Primrec.snd)
    have hbc : Primrec (fun p : Query × (List Nat × List Nat) => compileVectorCode p.2.2) :=
      ordinalSyntaxVectorCompilerPrimitiveRecursive.comp (Primrec.snd.comp Primrec.snd)
    have hboth := optionPairPrim hac hbc
    have h := Primrec.option_map hboth
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd).to₂
    apply h.of_eq
    intro p
    change (do let a ← compileVectorCode p.2.1; let b ← compileVectorCode p.2.2; pure (a,b)).map
      (fun ab => (p.1.2.1, ab)) = _
    cases compileVectorCode p.2.1 <;> cases compileVectorCode p.2.2 <;> rfl
  have h := Primrec.option_bind hpairs hc.to₂
  apply h.of_eq
  intro q
  dsimp only
  unfold compileSyntax
  cases DefaultSourceAssignment.assignmentCode (List.replicate q.1 0) q.2.2.1 <;>
    cases DefaultSourceAssignment.assignmentCode (List.replicate q.1 0) q.2.2.2 <;> rfl

theorem originalInputFrontendPrimitiveRecursive : Targets.OriginalInputFrontendPrimitiveRecursive := by
  have hdecode := originalInputCodecCorrect.2
  have hcompile := compileSyntaxPrimitiveRecursive.comp hdecode
  have hnormalize := Primrec.option_map hcompile
    (querySyntaxNormalizationPrimitiveRecursive.comp Primrec.snd).to₂
  have hquery := Primrec.option_getD.comp hnormalize (Primrec.const trueQuery)
  have h := Primrec.encode.comp ((Primrec.fst.comp hdecode).pair hquery)
  exact h.of_eq (fun n => rfl)

theorem originalInputFrontendArity : Targets.OriginalInputFrontendArity := by
  intro n
  simp [frontend, queryArity, decodeArityQuery]
end LogicLineages.OrdinalComparison.Source.OriginalInput

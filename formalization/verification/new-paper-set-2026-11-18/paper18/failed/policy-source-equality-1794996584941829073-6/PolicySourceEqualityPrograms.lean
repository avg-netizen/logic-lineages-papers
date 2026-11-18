module
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityTargets
public import LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
public import LogicLineages.OrdinalComparison.GroundSourceEqualityProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceEqualityPrograms
open OrdinalComparison Source Source.ForwardTranslation Source.OrdinalSyntax Source.AdmissibleSum
attribute [local irreducible] PolicyAssignment.assignmentCode GroundSourceEquality.queryEqualityFlag

theorem compile (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × Nat => PolicySourceEquality.compileSyntax p x.1 x.2.1 x.2.2) := by
  have hctx : Primrec (fun x : Nat × Nat × Nat => List.replicate x.1 0) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.fst (β := Nat × Nat)))
      (Primrec.const 0).to₂
    exact h.of_eq (fun x => by simp)
  have ha : Computable (fun x : Nat × Nat × Nat => PolicyAssignment.assignmentCode p (List.replicate x.1 0) x.2.1) :=
    (PolicyAssignmentRunPrograms.assignment p hp).comp
      (hctx.to_comp.pair (Computable.fst.comp Computable.snd))
  have hb : Computable (fun x : Nat × Nat × Nat => PolicyAssignment.assignmentCode p (List.replicate x.1 0) x.2.2) :=
    (PolicyAssignmentRunPrograms.assignment p hp).comp
      (hctx.to_comp.pair (Computable.snd.comp Computable.snd))
  have hc : Computable (fun x : (Nat × Nat × Nat) × List Nat × List Nat => do
      let ac ← compileVectorCode x.2.1
      let bc ← compileVectorCode x.2.2
      pure (false,ac,bc)) := by
    apply PolicyPartialMergePrograms.bindTwo
      (ordinalSyntaxVectorCompilerPrimitiveRecursive.to_comp.comp (Computable.fst.comp Computable.snd))
      (ordinalSyntaxVectorCompilerPrimitiveRecursive.to_comp.comp (Computable.snd.comp Computable.snd))
    exact Computable.option_some.comp ((Computable.const false).pair Computable.snd)
  exact PolicyPartialMergePrograms.bindTwo ha hb hc

theorem programs : PolicySourceEqualityTargets.Programs := by
  intro p hp
  have hs := compile p hp
  refine ⟨hs,?_⟩
  have hn : Computable₂ (fun _ : Nat × Nat × Nat => fun q : EncodedQuery =>
      GroundSourceEquality.queryEqualityFlag (normalizeQuerySyntaxCode q)) :=
    GroundSourceEquality.query_flag_computable.comp
      (querySyntaxNormalizationPrimitiveRecursive.to_comp.comp Computable.snd)
  exact Computable.option_getD (Computable.option_map hs hn) (Computable.const false)
end LogicLineages.StandardControlCurrent.PolicySourceEqualityPrograms

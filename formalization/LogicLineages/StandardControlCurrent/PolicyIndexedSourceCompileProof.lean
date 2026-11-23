module
public import LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompileTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentRunProof
import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerComputability

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompile
open OrdinalComparison Source Source.ForwardTranslation
open Source.OrdinalSyntax (compileVectorCode ordinalSyntaxVectorCompilerPrimitiveRecursive)
open PolicyIndexedAssignment (Node exactIndexedAssignmentRun)

theorem exactPolicyIndexedSourceCompile : ExactPolicyIndexedSourceCompile := by
  intro abs c p hp hb depth code
  unfold compile
  rw [exactIndexedAssignmentRun abs c p hp hb,Part.bind_some]
  rfl

private theorem finishPartrec : Partrec finish := by
  let V := PolicyIndexedAssignment.Value
  have h : Computable (fun v : V => v.bind compileVectorCode) :=
    Computable.option_bind Computable.id
      (ordinalSyntaxVectorCompilerPrimitiveRecursive.to_comp.comp Computable.snd).to₂
  exact Partrec.map (Computable.ofOption (Computable.id : Computable (id : Option V → Option V)))
    (h.comp Computable.snd).to₂

theorem policyIndexedSourceCompileEffectivity : PolicyIndexedSourceCompileEffectivity := by
  intro abs hr
  have depth : Primrec (fun x : Args => x.2.1) := Primrec.fst.comp Primrec.snd
  have rawContext : Primrec (fun x : Args => List.replicate x.2.1 (0 : Nat)) := by
    have h := Primrec.list_map (Primrec.list_range.comp depth) (Primrec.const 0).to₂
    exact h.of_eq (by intro x; simp)
  have rawCode : Computable (fun x : Args => x.2.2) :=
    Computable.snd.comp Computable.snd
  have run : Partrec (fun x : Args =>
      PolicyIndexedAssignment.run abs (x.1,List.replicate x.2.1 0,x.2.2)) :=
    hr.comp (Computable.fst.pair (rawContext.to_comp.pair rawCode))
  exact Partrec.bind run (finishPartrec.comp Computable.snd).to₂

end LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompile

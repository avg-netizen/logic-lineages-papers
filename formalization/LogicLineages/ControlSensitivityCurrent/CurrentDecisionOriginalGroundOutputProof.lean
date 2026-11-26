module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutputTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutput

open LogicLineages.OrdinalComparison.Source GroundEquivalence
open LogicLineages.StandardControlCurrent
open OriginalInput (Query)
open RawSourceDAG (Code)
open RawSourceDAG.PlanComparison (OutputCode)
open RawSourceDAG.InputCompiler (encodeInput)

theorem typedReencoding : CurrentDecisionOriginalGroundOutputTargets.TypedReencoding := by
  intro Γ a b strict
  change ((Γ.map SyntaxCode.typeCode).length,strict,CurrentTreeCode.expand (RawSourceDAG.encode ⟨Γ,.ground,a⟩),
    CurrentTreeCode.expand (RawSourceDAG.encode ⟨Γ,.ground,b⟩)) = literal strict a b
  rw [List.length_map, CurrentTreeCode.exactExpansion Γ .ground a, CurrentTreeCode.exactExpansion Γ .ground b] <;> rfl

private theorem reencodeExpected {Γ : List Ty} (r : InputNormalization.Input Γ 0) :
    let pr := InputNormalization.normalize .nil r
    outputQueries (CurrentCompiler.expected r) =
      (literal true (BooleanCompiler.strictPair pr).1 (BooleanCompiler.strictPair pr).2,
       literal false (BooleanCompiler.weakPair pr).1 (BooleanCompiler.weakPair pr).2) := by
  let pr := InputNormalization.normalize .nil r
  change (asTreeQuery true (RawPlanComparisonTargets.encodeComparison (BooleanCompiler.strictPair pr)),
    asTreeQuery false (RawPlanComparisonTargets.encodeComparison (BooleanCompiler.weakPair pr))) = _
  apply Prod.ext
  · exact typedReencoding _ _ _ true
  · exact typedReencoding _ _ _ false

theorem arithmeticOutputs : CurrentDecisionOriginalGroundOutputTargets.ArithmeticOutputs := by
  intro n r
  have h := (CurrentCompiler.StatementChecks.fixed_complete_compiler.2.1.1 n r).2
  rw [h]
  exact reencodeExpected r

theorem originalOutputs : CurrentDecisionOriginalGroundOutputTargets.OriginalOutputs := by
  intro p f hf n strict σ τ a b
  let q : Query := (n,strict,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
  obtain ⟨_,r,hA,hG,_,hS,hW⟩ :=
    CurrentDecisionTreePresentation.StatementChecks.exact_original_tree_queries p f hf n strict σ τ a b
  refine ⟨r,hA,?_,hS,hW⟩
  have hout : CurrentDecisionTreePresentation.toGround p f q = some (CurrentCompiler.expected r) := hG
  change (CurrentDecisionTreePresentation.toGround p f q).map outputQueries = _
  rw [hout, Option.map_some, reencodeExpected]

theorem effective : CurrentDecisionOriginalGroundOutputTargets.Effective := by
  let P := Bool × (Code × Code)
  have a : Primrec (fun x : P => x.2.1) := Primrec.fst.comp Primrec.snd
  have b : Primrec (fun x : P => x.2.2) := Primrec.snd.comp Primrec.snd
  have n := Primrec.list_length.comp (Primrec.fst.comp a)
  have one : Computable₂ asTreeQuery :=
    (n.pair (Primrec.fst.pair ((CurrentTreeCode.effective.comp a).pair
      (CurrentTreeCode.effective.comp b)))).to_comp.to₂
  have both : Computable outputQueries :=
    (one.comp (Computable.const true) Computable.fst).pair
      (one.comp (Computable.const false) (Computable.snd : Computable (fun o : OutputCode => o.2)))
  refine ⟨one,both,?_⟩
  intro p hp f hfc hf
  have g := (CurrentDecisionTreePresentation.StatementChecks.actual_effective_original_maps.2 p hp f hfc hf).2
  exact Computable.option_map g (both.comp Computable.snd).to₂

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutput

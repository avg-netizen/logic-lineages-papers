module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Program

attribute [local irreducible] Nat.sqrt Nat.unpair BalancedEvaluation.joint
  BalancedEvaluation.codeVariables BalancedRawCompiler.compileCode

private theorem input_shape : Computable (fun a : Input => a.1) := Computable.fst
private theorem input_tail1 : Computable (fun a : Input => a.2) := Computable.snd
private theorem input_certificate : Computable (fun a : Input => a.2.1) :=
  Computable.fst.comp input_tail1
private theorem input_tail2 : Computable (fun a : Input => a.2.2) :=
  Computable.snd.comp input_tail1
private theorem input_left : Computable (fun a : Input => a.2.2.1) :=
  Computable.fst.comp input_tail2
private theorem input_tail3 : Computable (fun a : Input => a.2.2.2) :=
  Computable.snd.comp input_tail2
private theorem input_right : Computable (fun a : Input => a.2.2.2.1) :=
  Computable.fst.comp input_tail3

/-- Both original supports use the accepted extractor at every raw shape,
including the empty shape. Deduplication changes only repeated raw names. -/
theorem rawSupport_computable : Computable (fun a : Input =>
    rawSupport a.1 a.2.1 a.2.2.1 a.2.2.2.1) := by
  have hl := BalancedBoxFormula.Program.variables_computable.comp
    (input_shape.pair (input_certificate.pair input_left))
  have hr := BalancedBoxFormula.Program.variables_computable.comp
    (input_shape.pair (input_certificate.pair input_right))
  exact BalancedBoxFormula.Program.dedup_primitive.to_comp.comp
    (Primrec.list_append.to_comp.comp hl hr)

attribute [local irreducible] rawSupport

/-- Only the literal tautological padding is asserted primitive recursive:
existing variable codes, existing equality instructions and finite conjunction. -/
theorem variablesCode_primitive : Primrec variablesCode := by
  have hv : Primrec (fun i : Nat => 4 * i + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id)
      (Primrec.const 1)
  have he : Primrec (fun i : Nat => ([(2, 4 * i + 1, 4 * i + 1)] : Code)) :=
    Primrec.list_cons.comp ((Primrec.const 2).pair (hv.pair hv)) (Primrec.const [])
  exact CommonHeadCode.Program.conjoin_primitive.comp
    (Primrec.list_map Primrec.id (he.comp Primrec.snd).to₂)

attribute [local irreducible] variablesCode

/-- Compose the unchanged total raw compiler with the actual original
support extractor and the literal padding. The full claim is Computable. -/
theorem outputCode_computable : Computable outputCode := by
  change Computable (fun a : Input =>
    CommonHeadCode.conjunction (BalancedRawCompiler.recursiveCode a)
      (variablesCode (rawSupport a.1 a.2.1 a.2.2.1 a.2.2.2.1)))
  exact CommonHeadCode.Program.conjunction_primitive.to_comp.comp
    BalancedRawCompiler.Proof.allCodeComputation.2
    (variablesCode_primitive.to_comp.comp rawSupport_computable)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Program

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof

theorem allCodeComputation : Targets.AllCodeComputation :=
  Program.outputCode_computable

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof

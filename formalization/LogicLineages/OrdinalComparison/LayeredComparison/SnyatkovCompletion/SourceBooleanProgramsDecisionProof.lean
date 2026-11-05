module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsRecursionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
open SourceBooleanPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair Code.shift

theorem test_primitive : Primrec Code.test := Primrec.fst.comp payload_primitive
theorem forest_primitive : Primrec Code.forest := Primrec.fst.comp (Primrec.snd.comp payload_primitive)
theorem predicate_primitive : Primrec Code.predicate := Primrec.snd.comp (Primrec.snd.comp payload_primitive)
theorem start_primitive : Primrec Code.start :=
  SourceRowsCodeProof.bound_primitive.comp (SourceTermGraphCodeProof.instructions_primitive.comp forest_primitive)

attribute [local irreducible] Code.test Code.forest Code.predicate Code.start

theorem graph_primitive : Primrec Code.graph := by
  have hs := SourceTermGraphCodeProof.run_primitive.comp
    (SourceTermGraphCodeProof.instructions_primitive.comp forest_primitive)
    (start_primitive.pair ((Primrec.const []).pair (Primrec.const [])))
  exact SourceTermGraphCodeProof.equations_primitive.comp (Primrec.snd.comp (Primrec.snd.comp hs))

attribute [local irreducible] Code.graph

theorem compile_primitive : Primrec Code.compile :=
  SourceTermGraphCodeProof.conjunction_primitive.comp graph_primitive
    (shift_primitive.comp start_primitive predicate_primitive)

attribute [local irreducible] Code.compile

theorem decideExists_primitive : Primrec Code.decideExists :=
  Primrec.ite (Primrec.eq.comp test_primitive (Primrec.const true))
    (Primrec.option_some.comp (PlainFrontierProgramsProof.answer_primitive.comp compile_primitive)) (Primrec.const none)

attribute [local irreducible] Code.decideExists

theorem decideForall_primitive : Primrec Code.decideForall :=
  Primrec.option_map (decideExists_primitive.comp (unary_primitive 5 2)) (Primrec.not.comp Primrec.snd).to₂

theorem actualNumericPrograms : SourceBooleanProgramsTargets.ActualNumericPrograms :=
  ⟨shift_primitive, payload_primitive, compile_primitive, decideExists_primitive, decideForall_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof

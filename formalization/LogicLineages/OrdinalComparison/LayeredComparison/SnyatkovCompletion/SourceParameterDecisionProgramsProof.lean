module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsDecisionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProof
open SourceParameterDecision
attribute [local irreducible] Nat.sqrt Nat.unpair SourceBooleanPrograms.Code.start
  SourceBooleanPrograms.Code.count SourceBooleanPrograms.Code.forest SourceBooleanPrograms.Code.compile
  SourceBooleanPrograms.Code.test

theorem witnesses_primitive : Primrec Code.witnesses :=
  SourceRowsCodeProof.names_primitive.comp SourceBooleanProgramsProof.start_primitive
    (SourceBooleanProgramsProof.count_primitive.comp SourceBooleanProgramsProof.forest_primitive)

attribute [local irreducible] Code.witnesses

theorem decideExists_primitive : Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideExists p.1 p.2.1 p.2.2) := by
  let A := List Nat × (List Nat × Nat)
  have ha : Primrec (fun p : A => (p.1 ++ Code.witnesses p.2.2, p.2.1, SourceBooleanPrograms.Code.compile p.2.2)) :=
    (Primrec.list_append.comp Primrec.fst (witnesses_primitive.comp (Primrec.snd.comp Primrec.snd))).pair
      ((Primrec.fst.comp Primrec.snd).pair
        (SourceBooleanProgramsProof.compile_primitive.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.ite (Primrec.eq.comp
    (SourceBooleanProgramsProof.test_primitive.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const true))
    (PlainParameterDecisionProof.decideExists_primitive.comp ha) (Primrec.const none)

attribute [local irreducible] Code.decideExists

theorem decideForall_primitive : Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideForall p.1 p.2.1 p.2.2) := by
  let A := List Nat × (List Nat × Nat)
  have ha : Primrec (fun p : A => (p.1, p.2.1, 5 * p.2.2 + 2)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      ((SourceBooleanProgramsProof.unary_primitive 5 2).comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.option_map (decideExists_primitive.comp ha) (Primrec.not.comp Primrec.snd).to₂

theorem actualNumericPrograms : SourceParameterDecisionTargets.ActualNumericPrograms :=
  ⟨witnesses_primitive, decideExists_primitive, decideForall_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProof

module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsProof
open PlainFrontierPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] PlainBranchSplitPrograms.Code.step
  MaximalPlainBranchPrograms.Code.variables MaximalPlainBranchPrograms.Code.isPlain

private theorem answersAny_primitive :
    Primrec (fun xs : List Nat => xs.any (fun p => (PlainBranchSplitPrograms.Code.step p).1)) := by
  have hs : Primrec (fun q : List Nat × (Nat × Bool) =>
      (PlainBranchSplitPrograms.Code.step q.2.1).1 || q.2.2) :=
    Primrec.or.comp
      (Primrec.fst.comp (PlainBranchSplitProgramsProof.step_primitive.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Nat => xs.foldr
      (fun p rest => (PlainBranchSplitPrograms.Code.step p).1 || rest) false) :=
    Primrec.list_foldr Primrec.id (Primrec.const false) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr_cons, List.any_cons, ih]

private theorem successors_primitive :
    Primrec (fun xs : List Nat => xs.flatMap (fun p => (PlainBranchSplitPrograms.Code.step p).2)) :=
  Primrec.list_flatMap Primrec.id
    (Primrec.snd.comp (PlainBranchSplitProgramsProof.step_primitive.comp Primrec.snd)).to₂

theorem advance_primitive : Primrec Code.advance :=
  (Primrec.or.comp Primrec.fst (answersAny_primitive.comp Primrec.snd)).pair
    (successors_primitive.comp Primrec.snd)

attribute [local irreducible] Code.advance

theorem run_primitive : Primrec₂ Code.run := by
  have hs : Primrec₂ (fun (_ : Nat × Code.State) (s : Code.State) => Code.advance s) :=
    advance_primitive.comp Primrec.snd
  exact Primrec.nat_iterate Primrec.fst Primrec.snd hs

theorem fuel_primitive : Primrec Code.fuel :=
  Primrec.nat_add.comp (Primrec.list_length.comp MaximalPlainBranchProgramsProof.variables_primitive) (Primrec.const 1)

theorem initial_primitive : Primrec Code.initial :=
  (Primrec.const false).pair (Primrec.list_cons.comp Primrec.id (Primrec.const []))

attribute [local irreducible] Code.run Code.fuel Code.initial

theorem answer_primitive : Primrec Code.answer :=
  Primrec.fst.comp (run_primitive.comp fuel_primitive initial_primitive)

attribute [local irreducible] Code.answer

theorem decide_primitive : Primrec Code.decide :=
  Primrec.ite (Primrec.eq.comp MaximalPlainBranchProgramsProof.isPlain_primitive (Primrec.const true))
    (Primrec.option_some.comp answer_primitive) (Primrec.const none)

theorem actualNumericPrograms : PlainFrontierProgramsTargets.ActualNumericPrograms :=
  ⟨advance_primitive, run_primitive, fuel_primitive, initial_primitive, answer_primitive, decide_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsProof

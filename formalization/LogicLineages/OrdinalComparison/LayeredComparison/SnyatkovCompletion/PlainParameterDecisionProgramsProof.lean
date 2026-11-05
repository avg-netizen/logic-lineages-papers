module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
open PlainParameterDecision
attribute [local irreducible] Nat.sqrt Nat.unpair MaximalPlainBranchPrograms.Code.variables
  MaximalPlainBranchPrograms.Code.isPlain

private theorem notContains_primitive : Primrec₂ (fun (xs : List Nat) (i : Nat) => !xs.contains i) := by
  have hm : PrimrecRel (fun (xs : List Nat) (i : Nat) => ∃ j ∈ xs, j = i) :=
    (show PrimrecRel (fun a b : Nat => a = b) from Primrec.eq).exists_mem_list
  have hn : PrimrecRel (fun (xs : List Nat) (i : Nat) => i ∉ xs) := hm.not.of_eq (by intros; simp)
  apply hn.decide.of_eq
  intro xs i
  by_cases h : i ∈ xs <;> simp [h]

theorem fixedNames_primitive : Primrec₂ Code.fixedNames :=
  (InactivePhiProgramsProof.filterWith_primitive notContains_primitive).comp Primrec.fst
    (MaximalPlainBranchProgramsProof.variables_primitive.comp Primrec.snd)

theorem pin_primitive : Primrec₂ Code.pin :=
  SourceTermGraphCodeProof.equation_primitive.comp SourceTermGraphCodeProof.numeralRow_primitive

attribute [local irreducible] Code.fixedNames Code.pin

theorem frame_primitive : Primrec (fun p : List Nat × (List Nat × Nat) => Code.frame p.1 p.2.1 p.2.2) := by
  let A := List Nat × (List Nat × Nat)
  have hs : Primrec (fun p : A × (Nat × Nat) =>
      SourceTermGraph.Code.conjunction (Code.pin p.2.1 (p.1.2.1.getD p.2.1 0)) p.2.2) :=
    SourceTermGraphCodeProof.conjunction_primitive.comp
      (pin_primitive.comp (Primrec.fst.comp Primrec.snd)
        ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A => (Code.fixedNames p.1 p.2.2).foldr
      (fun i rest => SourceTermGraph.Code.conjunction (Code.pin i (p.2.1.getD i 0)) rest) 0) :=
    Primrec.list_foldr (fixedNames_primitive.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (Primrec.const 0) hs.to₂
  exact SourceTermGraphCodeProof.conjunction_primitive.comp (Primrec.snd.comp Primrec.snd) hf

attribute [local irreducible] Code.frame

theorem decideExists_primitive : Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideExists p.1 p.2.1 p.2.2) :=
  Primrec.ite (Primrec.eq.comp
    (MaximalPlainBranchProgramsProof.isPlain_primitive.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const true))
    (Primrec.option_some.comp (PlainFrontierProgramsProof.answer_primitive.comp frame_primitive)) (Primrec.const none)

attribute [local irreducible] Code.decideExists

theorem decideForall_primitive : Primrec (fun p : List Nat × (List Nat × Nat) => Code.decideForall p.1 p.2.1 p.2.2) := by
  let A := List Nat × (List Nat × Nat)
  have ha : Primrec (fun p : A => (p.1, p.2.1, 6 * p.2.2 + 3)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.snd.comp Primrec.snd)) (Primrec.const 3)))
  exact Primrec.option_map (decideExists_primitive.comp ha) (Primrec.not.comp Primrec.snd).to₂

theorem actualNumericPrograms : PlainParameterDecisionTargets.ActualNumericPrograms :=
  ⟨frame_primitive, decideExists_primitive, decideForall_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof

module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaDataProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterDataProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationInterfacesProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationTableProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Program
open IntegerAlgorithms.Proof

attribute [local irreducible] Nat.sqrt Nat.unpair BalancedEvaluation.upperData
  BalancedEvaluation.certificateData BalancedEvaluation.valueAt BalancedEvaluation.variablesAt

private theorem map_computable {X Y Z : Type} [Primcodable X] [Primcodable Y]
    [Primcodable Z] [Inhabited Y] {xs : X → List Y} {f : X → Y → Z}
    (hx : Computable xs) (hf : Computable₂ f) :
    Computable (fun x => (xs x).map (f x)) := by
  have hs : Computable₂ (fun x : X => fun state : Y × List Z =>
      f x state.1 :: state.2) :=
    Primrec.list_cons.to_comp.comp
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (BalancedBoxEvaluation.Graph.computable_foldr default hx
    (Computable.const []) hs).of_eq
  intro x
  induction xs x with
  | nil => rfl
  | cons y ys ih => simp only [List.foldr_cons, List.map_cons, ih]

private theorem filter_computable {X Y : Type} [Primcodable X] [Primcodable Y]
    [Inhabited Y] {xs : X → List Y} {f : X → Y → Bool}
    (hx : Computable xs) (hf : Computable₂ f) :
    Computable (fun x => (xs x).filter (f x)) := by
  have hs : Computable₂ (fun x : X => fun state : Y × List Y =>
      cond (f x state.1) (state.1 :: state.2) state.2) :=
    Computable.cond
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Primrec.list_cons.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (BalancedBoxEvaluation.Graph.computable_foldr default hx
    (Computable.const []) hs).of_eq
  intro x
  induction xs x with
  | nil => rfl
  | cons y ys ih =>
    cases h : f x y <;> simp [List.filter_cons, h, ih]

private theorem input_k : Computable (fun p : Input => p.1) := Computable.fst
private theorem input_tail1 : Computable (fun p : Input => p.2) := Computable.snd
private theorem input_shape_tail : Computable (fun p : Input => p.2.1) :=
  Computable.fst.comp input_tail1
private theorem input_tail2 : Computable (fun p : Input => p.2.2) :=
  Computable.snd.comp input_tail1
private theorem input_certificate : Computable (fun p : Input => p.2.2.1) :=
  Computable.fst.comp input_tail2
private theorem input_tail3 : Computable (fun p : Input => p.2.2.2) :=
  Computable.snd.comp input_tail2
private theorem input_left : Computable (fun p : Input => p.2.2.2.1) :=
  Computable.fst.comp input_tail3
private theorem input_tail4 : Computable (fun p : Input => p.2.2.2.2) :=
  Computable.snd.comp input_tail3
private theorem input_right : Computable (fun p : Input => p.2.2.2.2.1) :=
  Computable.fst.comp input_tail4
private theorem input_desired : Computable (fun p : Input => p.2.2.2.2.2) :=
  Computable.snd.comp input_tail4
private theorem input_shape : Computable (fun p : Input => p.1 :: p.2.1) :=
  Primrec.list_cons.to_comp.comp input_k input_shape_tail

/-- Support uses the second component of the actual joint program. Its
finite table is irrelevant to this component, so the empty table suffices. -/
theorem variables_computable : Computable (fun p : List Nat × Nat × Nat =>
    BalancedEvaluation.codeVariables p.1 p.2.1 p.2.2) := by
  have hi : Computable (fun p : List Nat × Nat × Nat =>
      (p.1, p.2.1, p.2.2, ([] : List Nat))) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.snd.comp Computable.snd).pair (Computable.const [])))
  exact (Computable.snd.comp
    (BalancedBoxEvaluation.Proof.allCodeComputation.comp hi)).of_eq (fun _ => rfl)

attribute [local irreducible] BalancedEvaluation.joint BalancedEvaluation.codeVariables

theorem rawSupport_computable : Computable (fun p : Input =>
    rawSupport p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) := by
  have hl := variables_computable.comp
    (input_shape.pair (input_certificate.pair input_left))
  have hr := variables_computable.comp
    (input_shape.pair (input_certificate.pair input_right))
  exact dedup_primitive.to_comp.comp (Primrec.list_append.to_comp.comp hl hr)

attribute [local irreducible] rawSupport

theorem rawWords_computable : Computable (fun p : Input =>
    rawWords p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) := by
  have ht := BalancedSourceAdapter.Program.threshold_primitive.to_comp.comp
    (input_k.pair (input_left.pair input_right))
  exact words_primitive.to_comp.comp ht (Computable.list_length.comp rawSupport_computable)

attribute [local irreducible] rawWords

/-- Both natural values are obtained at the same actual finite table. Their
coercions are subtracted in Int before applying the actual integer sign. -/
theorem codeSign_computable : Computable₂ (fun p : Input => fun word : List Nat =>
    codeSign (p.1 :: p.2.1) p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      (rawSupport p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) word) := by
  have ht : Computable (fun p : Input × List Nat =>
      BalancedBoxEvaluation.finiteTable
        (rawSupport p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2.1) p.2) :=
    BalancedBoxEvaluation.Proof.finiteTable_computable.comp
      (rawSupport_computable.comp Computable.fst) Computable.snd
  have hl := BalancedBoxEvaluation.Proof.allCodeComputation.comp
    ((input_shape.comp Computable.fst).pair
      ((input_certificate.comp Computable.fst).pair
        ((input_left.comp Computable.fst).pair ht)))
  have hr := BalancedBoxEvaluation.Proof.allCodeComputation.comp
    ((input_shape.comp Computable.fst).pair
      ((input_certificate.comp Computable.fst).pair
        ((input_right.comp Computable.fst).pair ht)))
  have hleft := ofNat_primitive.to_comp.comp (Computable.fst.comp hl)
  have hright := ofNat_primitive.to_comp.comp (Computable.fst.comp hr)
  apply (sign_primitive.to_comp.comp
    (add_primitive.to_comp.comp hleft (negate_primitive.to_comp.comp hright))).of_eq
  intro p
  simp only [codeSign, sub_eq_add_neg]

attribute [local irreducible] codeSign pointCode

theorem formulaCode_computable : Computable (fun p : Input =>
    formulaCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have htest : Computable₂ (fun p : Input => fun word : List Nat =>
      decide (codeSign (p.1 :: p.2.1) p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        (rawSupport p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) word =
          p.2.2.2.2.2)) :=
    Primrec.eq.decide.to_comp.comp codeSign_computable
      (input_desired.comp Computable.fst)
  have hwords := filter_computable rawWords_computable htest
  have hpoint : Computable₂ (fun p : Input => fun word : List Nat =>
      pointCode (rawSupport p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1) word) :=
    pointCode_primitive.to_comp.comp (rawSupport_computable.comp Computable.fst)
      Computable.snd
  exact CommonHeadCode.Program.disjoin_primitive.to_comp.comp
    (map_computable hwords hpoint)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Program

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof

theorem allCodeComputation : Targets.AllCodeComputation :=
  Program.formulaCode_computable

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof

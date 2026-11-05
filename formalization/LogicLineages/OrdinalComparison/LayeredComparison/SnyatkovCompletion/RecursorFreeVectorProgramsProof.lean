module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionProgramsProof
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProgram
open RecursorFreeVector Source Source.ForwardTranslation

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem bool_and : Primrec₂ Bool.and := by
  apply (Primrec.cond Primrec.fst Primrec.snd (Primrec.const false)).of_eq
  intro p
  cases p.1 <;> rfl

theorem positive_primitive : Primrec (fun p : Nat × EncodedVector × EncodedVector => positiveFlag p.1 p.2.1 p.2.2) := by
  let A := Nat × EncodedVector × EncodedVector
  have hn : Primrec (fun v : EncodedVector => v.2.map encodedClosedPositive) :=
    Primrec.list_map Primrec.snd (encodedClosedPositivePrimitiveRecursive.comp Primrec.snd)
  have ha : Primrec (fun p : A => p.2.1.2.map encodedClosedPositive) := hn.comp (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2.map encodedClosedPositive) := hn.comp (Primrec.snd.comp Primrec.snd)
  have hab := positiveComparisonPrimitiveRecursive.comp ha hb
  have hba := positiveComparisonPrimitiveRecursive.comp hb ha
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) hab
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) hab (bool_and.comp hab hba))

theorem formula_primitive : Primrec (fun p : Nat × Nat × Nat × Nat => Code.formula p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × Nat × Nat × Nat
  have ha : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hlt : Primrec (fun p : A => ([(3,p.2.2.1,p.2.2.2)] : List CommonHeadCompiler.Instruction)) :=
    Primrec.list_cons.comp ((Primrec.const 3).pair (ha.pair hb)) (Primrec.const [])
  have hgt : Primrec (fun p : A => ([(3,p.2.2.2,p.2.2.1)] : List CommonHeadCompiler.Instruction)) :=
    Primrec.list_cons.comp ((Primrec.const 3).pair (hb.pair ha)) (Primrec.const [])
  have heq : Primrec (fun p : A => ([(2,p.2.2.1,p.2.2.2)] : List CommonHeadCompiler.Instruction)) :=
    Primrec.list_cons.comp ((Primrec.const 2).pair (ha.pair hb)) (Primrec.const [])
  have hm : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr := Primrec.ite (Primrec.eq.comp hm (Primrec.const 0))
    (CommonHeadCode.Program.negative_primitive.comp hgt)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) hlt heq)
  exact CommonHeadCode.Program.disjunction_primitive.comp
    (CommonHeadCode.Program.negative_primitive.comp
      (BalancedClosureDecisionProof.positiveCode_primitive.comp (Primrec.list_range.comp Primrec.fst))) hr

attribute [local irreducible] positiveFlag Code.formula

theorem vectors_computable : Computable Code.decideVectors := by
  let A := Code.VectorInput
  have ha : Computable (fun p : A => FiniteCoefficientBase.Code.compile p.2.2.1.1) :=
    FiniteCoefficientBaseProgram.compile_computable.comp
      (Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb : Computable (fun p : A => FiniteCoefficientBase.Code.compile p.2.2.2.1) :=
    FiniteCoefficientBaseProgram.compile_computable.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hf : Computable (fun p : A => positiveFlag p.2.1 p.2.2.1 p.2.2.2) :=
    positive_primitive.to_comp.comp Computable.snd
  have hform : Computable (fun p : A × Nat × Nat => Code.formula p.1.1 p.1.2.1 p.2.1 p.2.2) :=
    formula_primitive.to_comp.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
  have hd : Computable (fun p : A × Nat × Nat =>
      BaseBooleanSource.Code.decideClosureForall (Code.formula p.1.1 p.1.2.1 p.2.1 p.2.2)) :=
    BaseBooleanSourceProof.decideClosureForall_primitive.to_comp.comp hform
  have hm : Computable (fun p : A × Nat × Nat =>
      (BaseBooleanSource.Code.decideClosureForall (Code.formula p.1.1 p.1.2.1 p.2.1 p.2.2)).map
        (fun answer => positiveFlag p.1.2.1 p.1.2.2.1 p.1.2.2.2 && answer)) :=
    Computable.option_map hd
      (bool_and.to_comp.comp (hf.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
  have hi : Computable₂ (fun p : A => fun x : Nat =>
      (FiniteCoefficientBase.Code.compile p.2.2.2.1).bind (fun y =>
        (BaseBooleanSource.Code.decideClosureForall (Code.formula p.1 p.2.1 x y)).map
          (fun answer => positiveFlag p.2.1 p.2.2.1 p.2.2.2 && answer))) :=
    Computable.option_bind (hb.comp Computable.fst)
      (hm.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂
  apply (Computable.option_bind ha hi).of_eq
  intro p
  simp only [Code.decideVectors, Option.map_eq_bind]
  rfl

attribute [local irreducible] Code.decideVectors

theorem source_computable : Computable Code.decideSource := by
  let A := Code.Input
  have ha : Computable (fun p : A => GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.1)) :=
    GroundPositiveQuerySplit.Proof.vectorAt_primitive.to_comp.comp
      (Computable.fst.pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb : Computable (fun p : A => GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.2)) :=
    GroundPositiveQuerySplit.Proof.vectorAt_primitive.to_comp.comp
      (Computable.fst.pair (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hv : Computable (fun p : (A × EncodedVector) × EncodedVector =>
      Code.decideVectors (p.1.1.1,p.1.1.2.1,p.1.2,p.2)) :=
    vectors_computable.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd)))
  exact Computable.option_bind ha
    (Computable.option_bind (hb.comp Computable.fst) hv.to₂).to₂

theorem actualNumericPrograms : RecursorFreeVectorTargets.ActualNumericPrograms :=
  ⟨vectors_computable, source_computable⟩
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProgram

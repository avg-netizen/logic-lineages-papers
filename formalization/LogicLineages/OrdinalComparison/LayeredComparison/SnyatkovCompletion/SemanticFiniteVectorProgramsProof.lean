module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorProgram
open SemanticFiniteVector RecursorFreeVector Source Source.ForwardTranslation
attribute [local irreducible] Nat.sqrt Nat.unpair positiveFlag RecursorFreeVector.Code.formula

theorem vectors_computable : Computable SemanticFiniteVector.Code.decideVectors := by
  let A := SemanticFiniteVector.Code.VectorInput
  have ha : Computable (fun p : A => SemanticFiniteScalar.Code.compile p.2.2.1.1) :=
    SemanticFiniteScalarProgram.compile_computable.comp
      (Computable.fst.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb : Computable (fun p : A => SemanticFiniteScalar.Code.compile p.2.2.2.1) :=
    SemanticFiniteScalarProgram.compile_computable.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hf : Computable (fun p : A => positiveFlag p.2.1 p.2.2.1 p.2.2.2) :=
    RecursorFreeVectorProgram.positive_primitive.to_comp.comp Computable.snd
  have hform : Computable (fun p : A × Nat × Nat => RecursorFreeVector.Code.formula p.1.1 p.1.2.1 p.2.1 p.2.2) :=
    RecursorFreeVectorProgram.formula_primitive.to_comp.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
  have hd : Computable (fun p : A × Nat × Nat =>
      BaseBooleanSource.Code.decideClosureForall (RecursorFreeVector.Code.formula p.1.1 p.1.2.1 p.2.1 p.2.2)) :=
    BaseBooleanSourceProof.decideClosureForall_primitive.to_comp.comp hform
  have hm : Computable (fun p : A × Nat × Nat =>
      (BaseBooleanSource.Code.decideClosureForall (RecursorFreeVector.Code.formula p.1.1 p.1.2.1 p.2.1 p.2.2)).map
        (fun answer => positiveFlag p.1.2.1 p.1.2.2.1 p.1.2.2.2 && answer)) :=
    Computable.option_map hd
      (RecursorFreeVectorProgram.bool_and.to_comp.comp (hf.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
  have hi : Computable₂ (fun p : A => fun x : Nat =>
      (SemanticFiniteScalar.Code.compile p.2.2.2.1).bind (fun y =>
        (BaseBooleanSource.Code.decideClosureForall (RecursorFreeVector.Code.formula p.1 p.2.1 x y)).map
          (fun answer => positiveFlag p.2.1 p.2.2.1 p.2.2.2 && answer))) :=
    Computable.option_bind (hb.comp Computable.fst)
      (hm.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂
  apply (Computable.option_bind ha hi).of_eq
  intro p
  simp only [SemanticFiniteVector.Code.decideVectors, Option.map_eq_bind]
  rfl

attribute [local irreducible] SemanticFiniteVector.Code.decideVectors

theorem source_computable : Computable SemanticFiniteVector.Code.decideSource := by
  let A := SemanticFiniteVector.Code.Input
  have ha : Computable (fun p : A => GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.1)) :=
    GroundPositiveQuerySplit.Proof.vectorAt_primitive.to_comp.comp
      (Computable.fst.pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb : Computable (fun p : A => GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.2)) :=
    GroundPositiveQuerySplit.Proof.vectorAt_primitive.to_comp.comp
      (Computable.fst.pair (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hv : Computable (fun p : (A × EncodedVector) × EncodedVector =>
      SemanticFiniteVector.Code.decideVectors (p.1.1.1,p.1.1.2.1,p.1.2,p.2)) :=
    vectors_computable.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd)))
  exact Computable.option_bind ha
    (Computable.option_bind (hb.comp Computable.fst) hv.to₂).to₂

theorem actualNumericPrograms : SemanticFiniteVectorTargets.ActualNumericPrograms :=
  ⟨vectors_computable, source_computable⟩
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorProgram

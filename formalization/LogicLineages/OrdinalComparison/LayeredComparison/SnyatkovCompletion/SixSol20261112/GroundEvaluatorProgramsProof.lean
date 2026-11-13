module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceCompilerProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
open SourceDecision NonlinearProjectionCompletion BooleanGraphCodeProof
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

def termAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 10 = 0 then code / 10 else if code % 10 = 1 then 0
  else if code % 10 = 2 then values.getD 0 0 + values.getD 1 0
  else if code % 10 = 3 then values.getD 0 0 - values.getD 1 0
  else if code % 10 = 4 then (code / 10).unpair.1 * values.getD 0 0
  else if code % 10 = 5 then values.getD 0 0 / (code / 10).unpair.1
  else if code % 10 = 6 then Phi (values.getD 0 0)
  else if code % 10 = 7 then FixedSeedControlResidue.H (values.getD 0 0)
  else if code % 10 = 8 then SnyatkovInverse.phiInverse (values.getD 0 0)
  else SnyatkovInverse.hyperInverse (values.getD 0 0)

theorem termAssemble_primitive : Primrec₂ termAssemble := by
  let A := Nat × List Nat
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  have hc : Primrec (fun p : A => (p.1 / 10).unpair.1) := (left_primitive 10).comp Primrec.fst
  exact Primrec.ite ((tag_is 10 0).comp Primrec.fst) ((quotient_primitive 10).comp Primrec.fst)
    (Primrec.ite ((tag_is 10 1).comp Primrec.fst) (Primrec.const 0)
      (Primrec.ite ((tag_is 10 2).comp Primrec.fst) (Primrec.nat_add.comp h0 h1)
        (Primrec.ite ((tag_is 10 3).comp Primrec.fst) (Primrec.nat_sub.comp h0 h1)
          (Primrec.ite ((tag_is 10 4).comp Primrec.fst) (Primrec.nat_mul.comp hc h0)
            (Primrec.ite ((tag_is 10 5).comp Primrec.fst) (Primrec.nat_div.comp h0 hc)
              (Primrec.ite ((tag_is 10 6).comp Primrec.fst) (Phi_primrec.comp h0)
                (Primrec.ite ((tag_is 10 7).comp Primrec.fst) (FixedSeedControlResidue.Proof.H_primitive.comp h0)
                  (Primrec.ite ((tag_is 10 8).comp Primrec.fst)
                    (SnyatkovInverse.Proof.actualPrimitiveRecursion.1.comp h0)
                    (SnyatkovInverse.Proof.actualPrimitiveRecursion.2.1.comp h0)))))))))

theorem term_equation (code : Nat) : groundTerm code =
    termAssemble code ((ExpandedGraphCodeProof.countChildren code).map groundTerm) := by
  rw [groundTerm]
  split_ifs <;> simp_all [ExpandedGraphCodeProof.countChildren, termAssemble]

theorem groundTerm_computable : Computable groundTerm := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat Nat ExpandedGraphCodeProof.countChildren termAssemble id
    ExpandedGraphCodeProof.countChildren_primitive.to_comp termAssemble_primitive.to_comp Computable.id
    groundTerm ExpandedGraphCodeProof.countChildren_decreasing term_equation).2

def matrixAssemble (code : Nat) (values : List Bool) : Bool :=
  if code % 8 = 0 then true else if code % 8 = 1 then false
  else if code % 8 = 2 then groundTerm (code / 8).unpair.1 == groundTerm (code / 8).unpair.2
  else if code % 8 = 3 then decide (groundTerm (code / 8).unpair.1 < groundTerm (code / 8).unpair.2)
  else if code % 8 = 4 then decide ((code / 8).unpair.1 ∣ groundTerm (code / 8).unpair.2)
  else if code % 8 = 5 then !(values.getD 0 false)
  else if code % 8 = 6 then values.getD 0 false && values.getD 1 false
  else values.getD 0 false || values.getD 1 false

theorem matrixAssemble_computable : Computable₂ matrixAssemble := by
  let A := Nat × List Bool
  have h0 : Computable (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 1)
  have hl : Computable (fun p : A => (p.1 / 8).unpair.1) := (left_primitive 8).to_comp.comp Computable.fst
  have hr : Computable (fun p : A => (p.1 / 8).unpair.2) := (right_primitive 8).to_comp.comp Computable.fst
  have ha := groundTerm_computable.comp hl
  have hb := groundTerm_computable.comp hr
  have hdvd : Primrec₂ (fun a b : Nat => decide (a ∣ b)) := by
    apply (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).decide.of_eq
    intro p
    simp only [Nat.dvd_iff_mod_eq_zero]
  exact ComputableMapAtomsProof.computable_ite ((tag_is 8 0).comp Primrec.fst) (Computable.const true)
    (ComputableMapAtomsProof.computable_ite ((tag_is 8 1).comp Primrec.fst) (Computable.const false)
      (ComputableMapAtomsProof.computable_ite ((tag_is 8 2).comp Primrec.fst)
        (Primrec.beq.to_comp.comp ha hb)
        (ComputableMapAtomsProof.computable_ite ((tag_is 8 3).comp Primrec.fst)
          (Primrec.nat_lt.decide.to_comp.comp ha hb)
          (ComputableMapAtomsProof.computable_ite ((tag_is 8 4).comp Primrec.fst)
            (hdvd.to_comp.comp hl hb)
            (ComputableMapAtomsProof.computable_ite ((tag_is 8 5).comp Primrec.fst)
              (Primrec.not.to_comp.comp h0)
              (ComputableMapAtomsProof.computable_ite ((tag_is 8 6).comp Primrec.fst)
                (Primrec.and.to_comp.comp h0 h1) (Primrec.or.to_comp.comp h0 h1)))))))

theorem matrix_equation (code : Nat) : groundMatrix code =
    matrixAssemble code ((forestChildren code).map groundMatrix) := by
  rw [groundMatrix]
  split_ifs <;> simp_all [forestChildren, matrixAssemble]

theorem groundMatrix_computable : Computable groundMatrix := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat Bool forestChildren matrixAssemble id
    forestChildren_primitive.to_comp matrixAssemble_computable Computable.id
    groundMatrix forestChildren_decreasing matrix_equation).2

theorem answer_computable : Computable answer := groundMatrix_computable.comp eliminate_computable

theorem actualEvaluationPrograms : SourceDecisionTargets.ActualEvaluationPrograms :=
  ⟨groundTerm_computable, groundMatrix_computable, answer_computable⟩

#print axioms termAssemble_primitive
#print axioms term_equation
#print axioms groundTerm_computable
#print axioms matrixAssemble_computable
#print axioms matrix_equation
#print axioms groundMatrix_computable
#print axioms answer_computable
#print axioms actualEvaluationPrograms
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof

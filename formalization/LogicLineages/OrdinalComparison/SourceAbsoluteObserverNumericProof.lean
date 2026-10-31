module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerComputability
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

 theorem numeric_evaluator_computable : Computable (fun p : List Nat × Nat =>
    (((DefaultSourceAssignment.assignmentCode p.1 p.2).bind OrdinalSyntax.compileVectorCode).map
      (fun c => scalarSyntaxValue c.1 [])).getD 0) := by
  apply Computable.option_getD _ (Computable.const 0)
  apply Computable.option_map
  · exact Computable.option_bind DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.to_comp
      (OrdinalSyntax.ordinalSyntaxVectorCompilerPrimitiveRecursive.to_comp.comp Computable.snd).to₂
  · exact (scalarSyntaxValueComputable.comp
      ((Computable.fst.comp Computable.snd).pair (Computable.const []))).to₂

theorem open_evaluator_computable : Computable openSourceValue := by
  have hr : Primrec (fun n : Nat => List.replicate n (SyntaxCode.typeCode Ty.ground)) :=
    by
      have h := Primrec.list_map Primrec.list_range
        (Primrec.const (SyntaxCode.typeCode Ty.ground)).to₂
      apply h.of_eq
      intro n
      simp
  exact numeric_evaluator_computable.comp ((hr.to_comp.comp Computable.fst).pair Computable.snd)

theorem closed_evaluator_computable : Computable closedSourceValue :=
  numeric_evaluator_computable.comp ((Computable.const []).pair Computable.id)

theorem collapse_tail_strict (a : Ordinal) (ha : a < epsilonZero) :
    StrictMono (fun n : Nat => actualCollapse (a + (n : Ordinal))) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hk := actualFiniteTailClosureNorm a ha k
  have hs := actualFiniteTailClosureNorm a ha (k+1)
  have h := actualCollapse_controlledStrictness _ hs.1 (a+(k:Ordinal))
    (add_lt_add_right (by exact_mod_cast Nat.lt_succ_self k) a) (by
      rw [hk.2, hs.2]
      have hp := self_lt_Phi (actualOrdinalNorm a + (k+1))
      omega)
  omega

theorem scalar_positive {ι : Type} (s : Scalar ι) (ρ : ι → Nat) (hρ : ∀ i, 0 < ρ i) :
    0 < s.value ρ := by
  induction s with
  | one => exact Nat.zero_lt_one
  | var x => exact hρ x
  | add a b iha ihb => change 0 < a.value ρ + b.value ρ; omega
  | shift c a ih =>
    have hh := scalarFixedHeadAdmissible c
    have hb := actualFiniteTailClosureNorm (fixedHead c) hh.2 (a.value ρ)
    have hp : 0 < fixedHead c + (a.value ρ : Ordinal) :=
      Ordinal.omega0_pos.trans_le (hh.1.trans (le_add_right le_rfl : fixedHead c ≤ fixedHead c + (a.value ρ : Ordinal)))
    have h := actualCollapse_controlledStrictness _ hb.1 0 hp (by
      have hz : actualOrdinalNorm 0 = 0 := by simpa using (finiteNorm 0).2
      rw [hz]
      exact Nat.zero_le _)
    have hz := actualCollapse_finiteValues 0
    change 0 < actualCollapse (fixedHead c + (a.value ρ : Ordinal))
    simp only [Nat.cast_zero] at hz
    omega
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof

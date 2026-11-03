module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingCarrierProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof
open SourceUnaryChain.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem inactive_of_headFree {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hf : ordinalHeadFree q = true) :
    ¬ ActiveScalarAnnotation.Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q := by
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs] at hf
    | there x =>
      intro ha
      have he := List.mem_singleton.mp ha
      cases he
  | zero | one | omega => simp [ActiveScalarAnnotation.Active, AssignmentSupport.names,
      ordinalExpressionVariables]
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    have hparts : ordinalHeadFree a = true ∧ ordinalHeadFree b = true := by
      simpa [ordinalHeadFree, ordinalHeadOccurs] using hf
    intro ha
    have hm : ActiveScalarAnnotation.Active .here a ∨ ActiveScalarAnnotation.Active .here b := by
      simpa only [ActiveScalarAnnotation.Active, AssignmentSupport.Proof.names_add,
        AssignmentSupport.Proof.names_emul, AssignmentSupport.Proof.names_collapse,
        List.mem_append] using ha
    rcases hm with ha | hb
    · exact iha hparts.1 ha
    · exact ihb hparts.2 hb

theorem naturalSum_zero_right (a : Ordinal) : ordinalNaturalSum a 0 = a := by
  simpa using actualNaturalSumFiniteRight a 0

theorem naturalSum_zero_left (a : Ordinal) : ordinalNaturalSum 0 a = a := by
  rw [sum_comm, naturalSum_zero_right]

theorem carrierSum_append (xs ys : List Carrier) :
    carrierSum (xs ++ ys) = ordinalNaturalSum (carrierSum xs) (carrierSum ys) := by
  induction xs with
  | nil => simp [carrierSum, naturalSum_zero_left]
  | cons a xs ih => simp only [List.cons_append, carrierSum, ih, sum_assoc]

@[simp] theorem carrierSum_singleton (a : Carrier) : carrierSum [a] = a.head := by
  simp [carrierSum, naturalSum_zero_right]

theorem finite_tail_pair (a b : Ordinal) (m n : Nat) :
    ordinalNaturalSum (a + (m : Ordinal)) (b + (n : Ordinal)) =
      ordinalNaturalSum a b + ((m+n : Nat) : Ordinal) := by
  rw [← actualNaturalSumFiniteRight a m, ← actualNaturalSumFiniteRight b n]
  rw [sum_assoc a (m : Ordinal), ← sum_assoc (m : Ordinal) b,
    sum_comm (m : Ordinal) b, sum_assoc b (m : Ordinal), ← sum_assoc a b,
    naturalSum_finite, actualNaturalSumFiniteRight]

theorem finite_account_step (xs : List Carrier) (c n δ : Nat) :
    ordinalNaturalSum ((n : Ordinal) + (δ : Ordinal)) (carrierSum xs + (c : Ordinal)) =
      carrierSum xs + ((c+n+δ : Nat) : Ordinal) := by
  rw [sum_comm, ← Nat.cast_add, actualNaturalSumFiniteRight]
  simp only [Nat.cast_add, add_assoc]

theorem nonfinite_account_step (xs : List Carrier) (label : Carrier) (c δ : Nat) :
    ordinalNaturalSum (label.head + (δ : Ordinal)) (carrierSum xs + (c : Ordinal)) =
      carrierSum (xs ++ [label]) + ((c+δ : Nat) : Ordinal) := by
  rw [finite_tail_pair, carrierSum_append, carrierSum_singleton, sum_comm label.head,
    Nat.add_comm δ c]

end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof

module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveTargets
public import LogicLineages.ControlSensitivityCurrent.GenericScalarProof
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusProof
public import LogicLineages.PermittedControl.SelectedSumValueProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open ActiveScalarAnnotation AssignmentSupport AssignmentSupport.Proof
open AdmissibleSum ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)
open SourceUnaryChain.Proof (sum_comm sum_assoc)

theorem literalReserveRows : CurrentReserveTargets.LiteralReserveRows := by
  intro p a xs ys c d n δ
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [reserve,List.length_append,List.length_cons,
    List.length_nil,Nat.cast_add,Nat.cast_one,Nat.cast_zero] <;> omega

theorem reserveAdd {p : Policy} (xs ys : List (Carrier p)) (c d : Nat) :
    reserve (xs++ys) (c+d+1) = reserve xs c + reserve ys d + 1 := by
  simp only [reserve,List.length_append,Nat.cast_add,Nat.cast_one]
  omega

theorem reserveMonotone {p : Policy} {xs : List (Carrier p)} {c d : Nat} (h : c ≤ d) :
    reserve xs c ≤ reserve xs d := by
  have hh : (c : Int) ≤ (d : Int) := by exact_mod_cast h
  unfold reserve
  omega

theorem activeAdd {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) (a b : OrdinalExpression Γ) :
    Active F (.add a b) ↔ Active F a ∨ Active F b := by
  simp only [Active,names_add,List.mem_append]

theorem activeCollapse {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) (a b : OrdinalExpression Γ) :
    Active F (.collapse a b) ↔ Active F a ∨ Active F b := by
  simp only [Active,names_collapse,List.mem_append]

theorem inactiveOne {k Γ} (F : Variable Γ (Ty.curriedGround (k+1))) :
    ¬ Active F .one := by
  simp [Active,names,ordinalExpressionVariables]

theorem trackedActive {k : Nat} {Γ : List Ty} :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.var ⟨_,.here,0⟩) := by
  simp [Active,names,ordinalExpressionVariables,componentName]

theorem inactiveOfHeadFree {k Γ} (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hf : ordinalHeadFree q = true) : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q := by
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => simp [ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs] at hf
    | there x =>
      intro ha
      have he := List.mem_singleton.mp ha
      cases he
  | zero | one | omega => simp [Active,names,ordinalExpressionVariables]
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    have hp : ordinalHeadFree a = true ∧ ordinalHeadFree b = true := by
      simpa [ordinalHeadFree,ordinalHeadOccurs] using hf
    intro ha
    have hm : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) a ∨
        Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) b := by
      simpa only [Active,names_add,names_emul,names_collapse,List.mem_append] using ha
    exact hm.elim (iha hp.1) (ihb hp.2)

theorem activeNotHeadFree {k Γ} {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) : ordinalHeadFree q ≠ true :=
  fun h => inactiveOfHeadFree q h ha

theorem zeroUnits {Γ : List Ty} :
    commonUnits (fun _ : Variable Γ .ground => 0) = fun _ => 1 := by
  funext z
  rcases z with ⟨τ,x,j⟩
  cases τ with
  | ground =>
    change ((1 : Nat) : Ordinal) = 1
    exact Nat.cast_one
  | arrow a b => rfl

theorem unitPositive (f : Nat → Nat) {Γ i} (q : OrdinalExpression Γ)
    (hq : GeneratedOrdinalGrade Γ i q) : (1 : Ordinal) ≤ unitValue f q := by
  have hp := (GenericScalar.generatedPositiveFinite f Γ (fun _ => 0) i q hq).1
  apply Order.one_le_iff_pos.mpr
  simpa only [unitValue,zeroUnits,Nat.zero_add,Nat.cast_one] using hp

theorem natSumZeroRight (a : Ordinal) : ordinalNaturalSum a 0 = a := by
  simpa using actualNaturalSumFiniteRight a 0

theorem natSumZeroLeft (a : Ordinal) : ordinalNaturalSum 0 a = a := by
  rw [sum_comm,natSumZeroRight]

theorem carrierSumAppend {p : Policy} (f : Nat → Nat) (xs ys : List (Carrier p)) :
    carrierSum f (xs++ys) = ordinalNaturalSum (carrierSum f xs) (carrierSum f ys) := by
  induction xs with
  | nil => simp [carrierSum,natSumZeroLeft]
  | cons a xs ih => simp only [List.cons_append,carrierSum,ih,sum_assoc]

theorem carrierSumSingleton {p : Policy} (f : Nat → Nat) (a : Carrier p) :
    carrierSum f [a] = a.head f := by
  simp [carrierSum,natSumZeroRight]

theorem finiteTailPair (a b : Ordinal) (m n : Nat) :
    ordinalNaturalSum (a + (m : Ordinal)) (b + (n : Ordinal)) =
      ordinalNaturalSum a b + ((m+n : Nat) : Ordinal) := by
  rw [← actualNaturalSumFiniteRight a m,← actualNaturalSumFiniteRight b n]
  rw [sum_assoc a (m : Ordinal),← sum_assoc (m : Ordinal) b,
    sum_comm (m : Ordinal) b,sum_assoc b (m : Ordinal),← sum_assoc a b,
    naturalSum_finite,actualNaturalSumFiniteRight]

theorem finiteAccountStep {p : Policy} (f : Nat → Nat) (xs : List (Carrier p)) (c n δ : Nat) :
    ordinalNaturalSum ((n : Ordinal) + (δ : Ordinal)) (carrierSum f xs + (c : Ordinal)) =
      carrierSum f xs + ((c+n+δ : Nat) : Ordinal) := by
  rw [sum_comm,← Nat.cast_add,actualNaturalSumFiniteRight]
  simp only [Nat.cast_add,add_assoc]

theorem nonfiniteAccountStep {p : Policy} (f : Nat → Nat) (xs : List (Carrier p)) (label : Carrier p) (c δ : Nat) :
    ordinalNaturalSum (label.head f + (δ : Ordinal)) (carrierSum f xs + (c : Ordinal)) =
      carrierSum f (xs++[label]) + ((c+δ : Nat) : Ordinal) := by
  rw [finiteTailPair,carrierSumAppend,carrierSumSingleton,sum_comm (label.head f),Nat.add_comm δ c]

/-- Evaluate only AFTER the actual chosen-policy ternary syntax has been
formed by the partial. No chosen policy's original tree is changed. -/
theorem threeValue (p : Policy) (f : Nat → Nat) (site : MacroSite) {Γ : List Ty}
    (ν : OrdinalComponent Γ → Ordinal) (a b c : OrdinalExpression Γ) :
    denoteWith f ν (AdmissiblePartial.three p site a b c) =
      ordinalNaturalSum (ordinalNaturalSum (denoteWith f ν a) (denoteWith f ν b)) (denoteWith f ν c) := by
  unfold AdmissiblePartial.three
  rw [LogicLineages.PermittedControl.SelectedSumValueProof.sum_value f Γ 3
    (p.shape site 2) (OrdinalSyntax.leftShape 2) _ ν]
  rfl

end LogicLineages.ControlSensitivityCurrent.CurrentReserve

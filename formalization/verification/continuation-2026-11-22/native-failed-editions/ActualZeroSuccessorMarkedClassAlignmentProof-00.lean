module
public import LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClassTargets
import LogicLineages.PermittedControl.ActualFullValueLabelsProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClass
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (Label labels activeLabel exactFullValueLabels)
open ActualMixedRowLeadingAnnotations (Annotation AlignedAnnotations ActualAnnotation CountTailReady fullValue fullValues)
open ActualFullValueMaximalMetadata (exactActualMaximalMetadata)

private theorem lengths {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons x rest ih => exact congrArg Nat.succ ih

private theorem headStatus (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (t : WeightedOperand) (v : Nat) (a : Annotation)
    (actual : LowerOperandActual f ρ t.2 v) (read : lowerOperandRead f ρ t.2 = some (some v))
    (ann : ActualAnnotation f ρ t v a) (ready : t.1 ≠ 0 → CountTailReady ρ t.2) :
    (activeLabel t).isSome = (fullValue f a).isSome := by
  have one : AlignedAnnotations f ρ [t] [v] [a] := .cons actual read ann .nil
  have h := exactFullValueLabels f B selected ρ [t] [v] [a] one
    (fun u hu nz => by
      have same : u = t := List.mem_singleton.mp hu
      subst u
      exact ready nz)
  have len := lengths h
  cases hl : activeLabel t <;> cases hv : fullValue f a <;>
    simp [labels,fullValues,hl,hv] at len ⊢

theorem exactActualDecoration : ExactActualDecoration := by
  intro f B chosen ρ terms values anns aligned ready C
  induction aligned with
  | nil => rfl
  | @cons t terms v values a anns actual read ann _ ih =>
      have head := headStatus f B chosen ρ t v a actual read ann (ready t List.mem_cons_self)
      have tail := ih (fun u hu => ready u (List.mem_cons_of_mem _ hu))
      cases hl : activeLabel t <;> cases hv : fullValue f a <;>
        simp [hl,hv] at head <;>
        simp [decorate,hl,hv,fullValues,actualMarked,selected,tail]

theorem exactMatchedMaximalDecoration : ExactMatchedMaximalDecoration := by
  intro f B chosen ρ terms values anns aligned ready live a matched
  obtain ⟨C,largest,flags,_,_⟩ :=
    exactActualMaximalMetadata f B chosen ρ terms values anns aligned ready live a matched
  exact ⟨C,largest,by rw [flags,exactActualDecoration f B chosen ρ terms values anns aligned ready C]⟩

end LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClass

module
public import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataTargets
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataVectorProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataFlagsProof
import LogicLineages.PermittedControl.ActualFullValueLabelsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullValueMaximalMetadata
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (Label labels ActualLabel activeLabel exactFullValueLabels)
open ActualMixedRowLeadingAnnotations (Annotation AlignedAnnotations ActualAnnotation CountTailReady fullValue fullValues)
open ActualMixedRowLeadingSum (rowParts contribution)

private theorem alignedLength {α β : Type} {r : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ r xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons h hs next => exact congrArg Nat.succ next

private theorem status (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
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
  have len := alignedLength h
  cases hl : activeLabel t <;> cases hv : fullValue f a <;>
    simp [labels,fullValues,hl,hv] at len ⊢

private def selectedSum (C : Nat) (terms : List WeightedOperand) (vs : List Nat) : Int :=
  ((weights terms).zipWith (fun w b => if b then w else 0) (vs.map (fun v => decide (v = C)))).sum

private theorem signedMetadata (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand) (vs : List Nat) (anns : List Annotation)
    (aligned : AlignedAnnotations f ρ terms vs anns)
    (ready : ∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) :
    selectedSum C terms (fullValues f anns) = (rowParts f C terms vs anns).1 := by
  induction aligned with
  | nil => rfl
  | @cons t terms v vs a anns actual read ann tail ih =>
      have head := status f B selected ρ t v a actual read ann (ready t List.mem_cons_self)
      have rest := ih (fun u hu => ready u (List.mem_cons_of_mem _ hu))
      have impossibleSome (l : Label) (hl : activeLabel t = some l)
          (hn : fullValue f a = none) : False := by
        simpa [hl,hn] using head
      have impossibleNone (u : Nat) (hu : fullValue f a = some u)
          (hn : activeLabel t = none) : False := by
        simpa [hu,hn] using head
      cases a with
      | zeroWeight =>
          cases h : activeLabel t with
          | none =>
              simpa [selectedSum,weights,fullValues,h,fullValue,rowParts,contribution] using rest
          | some l => exact False.elim (impossibleSome l h rfl)
      | linear =>
          cases h : activeLabel t with
          | none =>
              simpa [selectedSum,weights,fullValues,h,fullValue,rowParts,contribution] using rest
          | some l => exact False.elim (impossibleSome l h rfl)
      | ordinary q =>
          obtain ⟨_,r,F,op,_,_,_⟩ := ann
          have w : doubledWeight t = 2*t.1 := by simp only [doubledWeight,op]
          cases h : activeLabel t with
          | none => exact False.elim (impossibleNone (f q) rfl h)
          | some l =>
              have step : (rowParts f C (t::terms) (v::vs) (.ordinary q::anns)).1 =
                  (if f q = C then 2*t.1 else 0) + (rowParts f C terms vs anns).1 := by
                by_cases through : f q = C <;> simp [rowParts,contribution,through]
              rw [step,← rest]
              simp [selectedSum,weights,fullValues,h,fullValue,w,List.zipWith]
      | count i q κ =>
          obtain ⟨_,r,lam,mu,op,_⟩ := ann
          have w : doubledWeight t = t.1 := by simp only [doubledWeight,op]
          cases h : activeLabel t with
          | none => exact False.elim (impossibleNone (f q) rfl h)
          | some l =>
              have step : (rowParts f C (t::terms) (v::vs) (.count i q κ::anns)).1 =
                  (if f q = C then t.1 else 0) + (rowParts f C terms vs anns).1 := by
                by_cases through : f q = C <;> simp [rowParts,contribution,through]
              rw [step,← rest]
              simp [selectedSum,weights,fullValues,h,fullValue,w,List.zipWith]

theorem exactActualMaximalMetadata : ExactActualMaximalMetadata := by
  intro f B selected ρ terms vs anns aligned ready nonempty as matched
  let actual := fullValues f anns
  have tape := exactFullValueLabels f B selected ρ terms vs anns aligned ready
  have same : as = numericVector actual :=
    (exactMatchedNumericVector f ρ (labels terms) actual tape as).mp matched
  have size : actual.length = (labels terms).length := (alignedLength tape).symm
  have active : actual ≠ [] := by
    intro empty
    rw [empty] at size
    cases h : labels terms with
    | nil => exact nonempty h
    | cons l ls =>
        rw [h] at size
        change 0 = ls.length+1 at size
        omega
  cases max : actual.max? with
  | none => exact False.elim (active (List.max?_eq_none_iff.mp max))
  | some C =>
      have flagsExact : classFlags (labels terms) as = actual.map (fun v => decide (v = C)) := by
        rw [same]
        exact exactNumericMaximumFlags (labels terms) actual size C max
      have coefficient : maximalCoefficient terms as = (rowParts f C terms vs anns).1 := by
        unfold maximalCoefficient
        rw [flagsExact]
        exact signedMetadata f B selected ρ C terms vs anns aligned ready
      exact ⟨C,rfl,flagsExact,coefficient,by rw [coefficient]⟩

end LogicLineages.PermittedControl.ActualFullValueMaximalMetadata

module
public import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClass
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (labels activeLabel)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (pairs Matches)
open ActualFullValueMaximalMetadata (classFlags)
open ActualMixedRowLeadingAnnotations (Annotation AlignedAnnotations CountTailReady fullValue fullValues)

abbrev Marked := WeightedOperand × Bool

/-- The mask advances at exactly the original active labeled
occurrences, even if field/rank syntax repeats. An exhausted or excess
mask is rejected rather than synthesizing a selection. -/
def decorate : List WeightedOperand → List Bool → Option (List Marked)
  | [], [] => some []
  | [], _::_ => none
  | t::ts, bs =>
      match activeLabel t,bs with
      | none,_ => (decorate ts bs).map (List.cons (t,false))
      | some _,[] => none
      | some _,b::rest => (decorate ts rest).map (List.cons (t,b))

def selected (f : Nat → Nat) (C : Nat) (a : Annotation) : Bool :=
  match fullValue f a with
  | none => false
  | some v => decide (v = C)

def actualMarked (f : Nat → Nat) (C : Nat)
    (terms : List WeightedOperand) (anns : List Annotation) : List Marked :=
  List.zipWith (fun t a => (t,selected f C a)) terms anns

def ExactDecorationDomain : Prop :=
  ∀ (ts : List WeightedOperand) (bs : List Bool),
    ((decorate ts bs).isSome = true ↔ bs.length = (labels ts).length) ∧
    ∀ ms : List Marked, decorate ts bs = some ms → ms.map Prod.fst = ts

def ExactActualDecoration : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat) (anns : List Annotation),
    AlignedAnnotations f ρ terms values anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    ∀ C : Nat,
      decorate terms ((fullValues f anns).map (fun v => decide (v = C))) =
        some (actualMarked f C terms anns)

def ExactMatchedMaximalDecoration : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat) (anns : List Annotation),
    AlignedAnnotations f ρ terms values anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    labels terms ≠ [] →
    ∀ a : List Answer, Matches f ρ (pairs (labels terms)) a →
      ∃ C : Nat, (fullValues f anns).max? = some C ∧
        decorate terms (classFlags (labels terms) a) = some (actualMarked f C terms anns)

def FullActualZeroSuccessorMarkedClass : Prop :=
  ExactDecorationDomain ∧ ExactActualDecoration ∧ ExactMatchedMaximalDecoration

end LogicLineages.PermittedControl.ActualZeroSuccessorMarkedClass

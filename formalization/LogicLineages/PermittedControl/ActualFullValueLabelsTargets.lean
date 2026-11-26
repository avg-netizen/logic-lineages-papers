module
public import LogicLineages.PermittedControl.ActualCountCoreLabelsTargets
public import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullValueLabels
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand orderedReads)
open ActualMixedRowLeadingAnnotations (AlignedAnnotations CountTailReady fullValues)

structure Label where
  rank : Nat
  field : ValueField

def operandLabel : LowerOperand → Option Label
  | .coordinate _ | .ordinary _ (.iterate 0) => none
  | .ordinary r F => some ⟨r,F⟩
  | .count r lam mu => (ActualCountCoreLabels.fieldLabel lam mu).map (fun F => ⟨r,F⟩)

/-- Keep exactly the active original nonlinear occurrences in literal
order. Repeated fields, ranks and labels are not deduplicated. -/
def activeLabel (t : WeightedOperand) : Option Label :=
  if t.1 = 0 then none else operandLabel t.2

def labels (terms : List WeightedOperand) : List Label := terms.filterMap activeLabel

def ActualLabel (f ρ : Nat → Nat) (l : Label) (v : Nat) : Prop :=
  ProperField l.field ∧
    LowerOperandActual f ρ (.ordinary l.rank l.field) v ∧
    lowerOperandRead f ρ (.ordinary l.rank l.field) = some (some v)

def ExactFullValueLabels : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat)
    (annotations : List ActualMixedRowLeadingAnnotations.Annotation),
    AlignedAnnotations f ρ terms values annotations →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
      List.Forall₂ (ActualLabel f ρ) (labels terms) (fullValues f annotations)

def ExactOriginalReadsHaveFullLabels : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat),
    orderedReads f ρ terms values → (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
      ∃ annotations, AlignedAnnotations f ρ terms values annotations ∧
        List.Forall₂ (ActualLabel f ρ) (labels terms) (fullValues f annotations)

def FullActualFullValueLabels : Prop :=
  ExactFullValueLabels ∧ ExactOriginalReadsHaveFullLabels

end LogicLineages.PermittedControl.ActualFullValueLabels

module
public import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsTargets
public import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullValueMaximalMetadata
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualFullValueLabels (Label labels ActualLabel activeLabel)
open ActualFullLabelPairGuards (Answer)
open ActualFiniteFullValueGuards (pairs Matches)
open ActualMixedRowLeadingAnnotations (Annotation AlignedAnnotations CountTailReady fullValues)
open ActualMixedRowLeadingSum (rowParts)

def compare (u v : Nat) : Answer :=
  if u < v then .less else if u = v then .equal else .greater

def numericVector (values : List Nat) : List Answer :=
  values.flatMap fun u => values.map (compare u)

def notLess (a : Answer) : Bool :=
  match a with
  | .less => false
  | .equal | .greater => true

def flags (width : Nat) : Nat → List Answer → List Bool
  | 0,_ => []
  | n+1,as => ((as.take width).all notLess) :: flags width n (as.drop width)

def classFlags (ls : List Label) (as : List Answer) : List Bool :=
  flags ls.length ls.length as

def doubledWeight (t : WeightedOperand) : Int :=
  match t.2 with
  | .ordinary .. => 2 * t.1
  | .count .. => t.1
  | .coordinate .. => 0

def weights (terms : List WeightedOperand) : List Int :=
  terms.filterMap fun t => (activeLabel t).map (fun _ => doubledWeight t)

/-- The candidate vector, not the actual unknown numerical maximum,
selects the class. Weights are retained in literal occurrence order. -/
def maximalCoefficient (terms : List WeightedOperand) (as : List Answer) : Int :=
  ((weights terms).zipWith
    (fun w b => if b then w else 0) (classFlags (labels terms) as)).sum

def ExactMatchedNumericVector : Prop :=
  ∀ (f θ : Nat → Nat) (ls : List Label) (vs : List Nat),
    List.Forall₂ (ActualLabel f θ) ls vs → ∀ as : List Answer,
      Matches f θ (pairs ls) as ↔ as = numericVector vs

def ExactNumericMaximumFlags : Prop :=
  ∀ (ls : List Label) (vs : List Nat), vs.length = ls.length →
    ∀ C : Nat, vs.max? = some C →
      classFlags ls (numericVector vs) = vs.map (fun v => decide (v = C))

def ExactActualMaximalMetadata : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (terms : List WeightedOperand) (vs : List Nat) (anns : List Annotation),
    AlignedAnnotations f ρ terms vs anns →
    (∀ t ∈ terms, t.1 ≠ 0 → CountTailReady ρ t.2) →
    labels terms ≠ [] →
    ∀ as : List Answer, Matches f ρ (pairs (labels terms)) as →
    ∃ C : Nat, (fullValues f anns).max? = some C ∧
      classFlags (labels terms) as = (fullValues f anns).map (fun v => decide (v = C)) ∧
      maximalCoefficient terms as = (rowParts f C terms vs anns).1 ∧
      (maximalCoefficient terms as = 0 ↔ (rowParts f C terms vs anns).1 = 0)

def FullActualFullValueMaximalMetadata : Prop :=
  ExactMatchedNumericVector ∧ ExactNumericMaximumFlags ∧ ExactActualMaximalMetadata

end LogicLineages.PermittedControl.ActualFullValueMaximalMetadata

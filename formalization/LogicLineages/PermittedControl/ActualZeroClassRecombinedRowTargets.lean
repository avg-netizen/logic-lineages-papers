module
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassRecombinedRow
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum ActualZeroClassReplacement
open ActualZeroClassCohortTransfer

/-- Preserve the order and values of every read outside the selected
proper-long prefix cohort. The constant comes from the full replacement. -/
noncomputable def outsideCohort (f : Nat → Nat) (C : Nat) :
    List WeightedOperand → List Nat → List Annotation → List Read
  | t::terms,v::values,ann::annotations =>
      let head := match survivingPrefix f C t ann with
        | none => (replaceOccurrence f C t v ann).1.toList
        | some _ => []
      head ++ outsideCohort f C terms values annotations
  | _,_,_ => []

def ExactResidualPartition : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (C : Nat) (terms : List WeightedOperand)
    (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations → Ready f B ρ C terms annotations →
    let out := replaceRow f C terms values annotations
    let outside := outsideCohort f C terms values annotations
    let active := (cohort f C terms annotations).map SurvivingPrefix.asRead
    outside.Sublist out.1 ∧ (outside ++ active).Perm out.1 ∧
      liftedReads f ρ outside ∧ readSum outside + readSum active = readSum out.1

/-- Replace the actual zero class and move exactly its surviving cohort
to the selected lowest rank. The output keeps all other residual reads
and the complete signed constant, including when all prefixes ended. -/
def ExactRecombinedZeroClassRow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (z C : Nat) (c : Int) (terms : List WeightedOperand)
    (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations → Ready f B ρ C terms annotations →
    (∀ t ∈ terms, ρ t.2.rank ≤ z) →
    C ∈ fullValues f annotations → (∀ D ∈ fullValues f annotations, D ≤ C) → f z ≤ C →
    (rowParts f C terms values annotations).1 = 0 →
    let ps := cohort f C terms annotations
    TransferReady B ρ ps →
    let out := replaceRow f C terms values annotations
    let outside := outsideCohort f C terms values annotations
    ∃ moved : List Read,
      (match leastPrefix ps with
      | none => ps = [] ∧ moved = []
      | some anchor => anchor ∈ ps ∧ (∀ p ∈ ps, anchor.rank ≤ p.rank) ∧
        MovedPrefixes f ρ anchor ps moved ∧
        ∀ r ∈ moved, r.1.2.rank = anchor.rank) ∧
      liftedReads f ρ (outside ++ moved) ∧
      c + actualSum terms values = (c + out.2) + readSum (outside ++ moved)

def FullActualZeroClassRecombinedRow : Prop :=
  ExactResidualPartition ∧ ExactRecombinedZeroClassRow

end LogicLineages.PermittedControl.ActualZeroClassRecombinedRow

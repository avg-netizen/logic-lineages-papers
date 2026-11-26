module
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassCommonTail
open OrdinalComparison FieldComparison MixedSameRankResidue
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualZeroClassCohortTransfer
open ConcreteCountPairReplacement
open SelectedCountOnlyClass (prefixTarget)

/-- The original raw rank and the exact source-to-prefix interval.
No selected class, actual read, annotation or valuation is used. -/
structure PrefixLabel where
  rank : Nat
  lam : NONote
  eta : NONote

def prefixLabel (t : WeightedOperand) : Option PrefixLabel :=
  match t.2 with
  | .count rank lam mu => some ⟨rank, lam, prefixTarget mu⟩
  | _ => none

def prefixLabels (terms : List WeightedOperand) : List PrefixLabel :=
  terms.filterMap prefixLabel

def survivorLabel (p : SurvivingPrefix) : PrefixLabel :=
  ⟨p.rank, p.lam, p.eta⟩

noncomputable def prefixAffordability (B : Nat) (label : PrefixLabel) : Nat :=
  max (actualOrdinalNorm label.lam.1.repr)
    (max (actualOrdinalNorm label.eta.1.repr + 3) (max 1 B))

/-- The original safe max of inverse-table and encoded gap-input tails,
in the order higher source P and lower anchor Q. -/
def labelPairTail (B : Nat) (anchor p : PrefixLabel) : Nat :=
  safeTailCode (intervalPairCodes p.lam p.eta anchor.lam anchor.eta) B

def finiteMax {α : Type} (cost : α → Nat) (xs : List α) : Nat :=
  xs.foldr (fun a bound => max (cost a) bound) 0

/-- Sufficient numerical tail for this one finite source node. All ordered
pairs are included, even those later ruled out by actual guards. -/
noncomputable def commonTail (B : Nat) (terms : List WeightedOperand) : Nat :=
  let labels := prefixLabels terms
  max (finiteMax (prefixAffordability B) labels)
    (finiteMax (fun anchor => finiteMax (labelPairTail B anchor) labels) labels)

def ExactCohortLabelProvenance : Prop :=
  ∀ (f : Nat → Nat) (C : Nat) (terms : List WeightedOperand) (annotations : List Annotation),
    ∀ p ∈ cohort f C terms annotations, survivorLabel p ∈ prefixLabels terms

/-- One source-only bound supplies the original selected-short guard and
both raw-input bounds on every actual higher transfer. The annotations
are given, not constructed. Their long shape and annotation tail are
not paid here; neither is the numeric premise that the coordinates
are in this tail. This implication does not require C to be maximal. -/
def ExactCommonTailGuards : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (C : Nat)
    (terms : List WeightedOperand) (values : List Nat) (annotations : List Annotation),
    AlignedAnnotations f ρ terms values annotations →
    (∀ label ∈ prefixLabels terms, commonTail B terms ≤ ρ label.rank) →
    Ready f B ρ C terms annotations ∧ TransferReady B ρ (cohort f C terms annotations)

def FullActualZeroClassCommonTail : Prop :=
  ExactCohortLabelProvenance ∧ ExactCommonTailGuards

end LogicLineages.PermittedControl.ActualZeroClassCommonTail

module
public import LogicLineages.PermittedControl.ActualWeightedReadNormalizationTargets
public import LogicLineages.PermittedControl.ActualFullValueLabelsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedNormalizationSyntax
open PreparedProjection
open MixedSameRankResidue (WeightedOperand orderedReads)
open ActualZeroClassReplacement (Read liftedReads)
open ActualWeightedReadNormalization (normalizeReads)
open ActualFullValueLabels (Label ActualLabel)

noncomputable def syntaxWeights : List WeightedOperand → LowerOperand →₀ Int
  | [] => 0
  | t::ts => Finsupp.single t.2 t.1 + syntaxWeights ts

noncomputable def normalizedTerms (terms : List WeightedOperand) : List WeightedOperand :=
  let weights := syntaxWeights terms
  weights.support.toList.map (fun op => (weights op,op))

def LowerStrict (ρ : Nat → Nat) (top : Nat) : Prop :=
  ∀ i j : Nat, i < j → j < top → ρ i < ρ j

def AboveLower (ρ : Nat → Nat) (top z : Nat) : Prop :=
  ∀ i : Nat, i < top → ρ i < z

/-- Strictly extend above the actual active rank support. This is not
the old raw update at unrelated, unused coordinates beyond top. -/
def extend (ρ : Nat → Nat) (top z : Nat) (i : Nat) : Nat :=
  if i < top then ρ i else z + (i-top)

def AgreeThrough (ρ σ : Nat → Nat) (top : Nat) : Prop :=
  ∀ i : Nat, i ≤ top → ρ i = σ i

def ExactNormalizedTermSkeleton : Prop :=
  (∀ (f ρ : Nat → Nat) (source xs : List Read), normalizeReads f ρ source = some xs →
    xs.map Prod.fst = normalizedTerms (source.map Prod.fst)) ∧
  ∀ (terms : List WeightedOperand) (t : WeightedOperand), t ∈ normalizedTerms terms →
    t.1 ≠ 0 ∧ ∃ u ∈ terms, u.2 = t.2

def ExactOriginalSupportRankExtension : Prop :=
  ∀ (ρ : Nat → Nat) (top z : Nat), LowerStrict ρ top → AboveLower ρ top z →
    StrictMono (extend ρ top z) ∧ extend ρ top z top = z ∧
      AgreeThrough (extend ρ top z) (Function.update ρ top z) top

def ExactOriginalRankReadLocality : Prop :=
  ∀ (f ρ σ : Nat → Nat) (top : Nat), AgreeThrough ρ σ top →
    (∀ op : LowerOperand, op.rank ≤ top →
      lowerOperandRead f ρ op = lowerOperandRead f σ op ∧
        ∀ v : Nat, LowerOperandActual f ρ op v ↔ LowerOperandActual f σ op v) ∧
    (∀ terms : List WeightedOperand, (∀ t ∈ terms, t.2.rank ≤ top) →
      ∀ vs : List Nat, orderedReads f ρ terms vs ↔ orderedReads f σ terms vs) ∧
    (∀ (l : Label), l.rank ≤ top → ∀ v : Nat, ActualLabel f ρ l v ↔ ActualLabel f σ l v) ∧
    ∀ (ops : List LowerOperand) (ν : Nat → Nat),
      PreparedTableTied f top ρ ops ν ↔ PreparedTableTied f top σ ops ν

def FullActualRankedNormalizationSyntax : Prop :=
  ExactNormalizedTermSkeleton ∧ ExactOriginalSupportRankExtension ∧ ExactOriginalRankReadLocality

end LogicLineages.PermittedControl.ActualRankedNormalizationSyntax

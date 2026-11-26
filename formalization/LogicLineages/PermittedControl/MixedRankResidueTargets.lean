module
public import LogicLineages.PermittedControl.MixedSameRankResidueTargets

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankResidue
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted properOperand
  orderedReads actualSum weightedResidue weightedResidueCode weightedTailCode)

abbrev Residues := List (Nat × Nat)

def rankPresent (rank : Nat) (ranks : List Nat) : Bool :=
  ranks.foldr (fun r found => if r = rank then true else found) false

def recordRank (rank : Nat) (ranks : List Nat) : List Nat :=
  if rankPresent rank ranks then ranks else rank :: ranks

def rankSupport (terms : List WeightedOperand) : List Nat :=
  terms.foldr (fun t ranks => recordRank t.2.rank ranks) []

def rankSupportCode (terms : List WeightedCode) : List Nat :=
  terms.foldr (fun t ranks => recordRank t.2.2.1 ranks) []

def lookup (rank : Nat) (entries : Residues) : Nat :=
  entries.foldr (fun e found => if e.1 = rank then e.2 else found) 0

def originalVector (m : Nat) (terms : List WeightedOperand) (ρ : Nat → Nat) : Residues :=
  (rankSupport terms).map (fun rank => (rank,ρ rank % (2*m)))

noncomputable def residueVector (terms : List WeightedOperand) (entries : Residues) : Int :=
  terms.foldr (fun t acc => weightedResidue [t] (lookup t.2.rank entries) + acc) 0

def residueVectorCode (terms : List WeightedCode) (entries : Residues) : Int :=
  terms.foldr (fun t acc => weightedResidueCode [t] (lookup t.2.2.1 entries) + acc) 0

def CodeExact : Prop :=
  Primrec rankSupportCode ∧ Primrec₂ residueVectorCode ∧
  (∀ terms : List WeightedOperand, rankSupportCode (terms.map encodeWeighted) = rankSupport terms) ∧
  ∀ (terms : List WeightedOperand) (entries : Residues),
    residueVectorCode (terms.map encodeWeighted) entries = residueVector terms entries

def RankSupport : Prop :=
  (∀ terms : List WeightedOperand, (rankSupport terms).Nodup ∧
    ∀ rank, rank ∈ rankSupport terms ↔ ∃ t ∈ terms, t.2.rank = rank) ∧
  ∀ (m : Nat) (terms : List WeightedOperand) (ρ : Nat → Nat) (rank : Nat),
    rank ∈ rankSupport terms → lookup rank (originalVector m terms ρ) = ρ rank % (2*m)

/-- One common computable tail is paid at every used raw rank. Every actual
operand is read at that original rank, with a shared residue there. -/
def ActualMultiRankResidue : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (m : Nat) (c : Int) (terms : List WeightedOperand) (ρ : Nat → Nat),
      0 < m → (∀ t ∈ terms, properOperand t.2) →
      (∀ rank ∈ rankSupport terms, weightedTailCode B m (terms.map encodeWeighted) ≤ ρ rank) →
      ∃ values : List Nat, orderedReads f ρ terms values ∧
        Int.ModEq (m : Int) (c + actualSum terms values) (c + residueVector terms (originalVector m terms ρ))

def FullMixedRankResidue : Prop := CodeExact ∧ RankSupport ∧ ActualMultiRankResidue

end LogicLineages.PermittedControl.MixedRankResidue

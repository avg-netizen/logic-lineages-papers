module
public import LogicLineages.PermittedControl.AffineCollapseGuardedLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapsePairListLow
open OrdinalComparison
open AffineCollapseGraphComposition (Expression graph)
open HeterogeneousSignedMatrixSlice (Row RawRow Snapshot actualRows encodeRow HitRows)
open HeterogeneousSignedMatrixLowStrips (RawBranch branches branchesCode encodeBranch)
open AffineCollapseGuardedLow (PairData guardRowsCode originalGuardSnapshot OriginalTestAt)

abbrev Pair := NONote × Expression × Nat × Nat
abbrev Args := Nat × Nat × List PairData × List RawRow

def encodePair (p : Pair) : PairData :=
  (rawNoteEncode p.1.1,p.2)

def LimitHeads (pairs : List Pair) : Prop :=
  ∀ p ∈ pairs, Order.IsSuccLimit p.1.1.repr

def GraphsAt (f θ : Nat → Nat) (pairs : List Pair) : Prop :=
  ∀ p ∈ pairs, graph f (rawNoteEncode p.1.1) p.2.1 p.2.2.1 p.2.2.2 θ

noncomputable def prefixRows : List Pair → List Row :=
  List.foldr (fun p rest =>
    AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2 ++ rest) []

noncomputable def prefixSnapshot (θ : Nat → Nat) : List Pair → Snapshot :=
  List.foldr (fun p rest => originalGuardSnapshot p.1 p.2.2.1 θ ++ rest) []

def prefixCode : List PairData → List RawRow :=
  List.foldr (fun p rest => guardRowsCode p ++ rest) []

noncomputable def listBranchesCode (f : Nat → Nat) (p : Args) : List RawBranch :=
  branchesCode f (p.1,p.2.1,prefixCode p.2.2.1 ++ p.2.2.2)

/-- One actual valuation for every occurrence in every pair. No fresh
binding is inferred from the order of the supplied list. -/
def ExactSharedPrefix : Prop :=
  ∀ (f θ : Nat → Nat) (pairs : List Pair), LimitHeads pairs →
    (actualRows f θ (prefixRows pairs) (prefixSnapshot θ pairs) ↔ GraphsAt f θ pairs)

def ExactListBranchCode : Prop :=
  Primrec prefixCode ∧
  (∀ f : Nat → Nat, Computable f → Computable (listBranchesCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), (listBranchesCode f p).map Prod.fst = List.range p.2.1) ∧
  ∀ (f : Nat → Nat) (pairs : List Pair) (rank bound : Nat) (testRows : List Row),
    listBranchesCode f (rank,bound,pairs.map encodePair,testRows.map encodeRow) =
      (branches f rank bound (prefixRows pairs ++ testRows)).map encodeBranch

def ExactFiniteListLow : Prop :=
  ∀ (f ρ : Nat → Nat) (prior : (Nat → Nat) → Prop) (pairs : List Pair), LimitHeads pairs →
    ∀ (rank bound : Nat) (testRows : List Row)
      (test : (Nat → Nat) → Snapshot → Prop) (positive : Bool),
      (∃ a : Nat, a < bound ∧
        let θ := Function.update ρ rank a
        prior θ ∧ GraphsAt f θ pairs ∧ ∃ testValues : Snapshot,
          actualRows f θ testRows testValues ∧ OriginalTestAt test positive θ testValues) ↔
      ∃ branch residual,
        branch ∈ branches f rank bound (prefixRows pairs ++ testRows) ∧ HitRows branch.2 residual ∧
        let θ := Function.update ρ rank branch.1
        prior θ ∧ ∃ testValues : Snapshot,
          actualRows f θ residual (prefixSnapshot θ pairs ++ testValues) ∧
            OriginalTestAt test positive θ testValues

def FullAffineCollapsePairListLow : Prop :=
  ExactSharedPrefix ∧ ExactListBranchCode ∧ ExactFiniteListLow

end LogicLineages.PermittedControl.AffineCollapsePairListLow

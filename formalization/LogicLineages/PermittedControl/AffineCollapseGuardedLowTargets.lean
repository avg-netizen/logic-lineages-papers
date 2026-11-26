module
public import LogicLineages.PermittedControl.AffineCollapseGuardRowsTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGuardedLow
open OrdinalComparison PreparedProjection
open AffineCollapseGraphComposition (Expression graph)
open HeterogeneousSignedMatrixSlice (Row RawRow Snapshot actualRows encodeRow HitRows)
open HeterogeneousSignedMatrixLowStrips (RawBranch branches branchesCode encodeBranch)
open MixedSameRankResidue (WeightedCode)

abbrev PairData := Nat × Expression × Nat × Nat
abbrev Args := Nat × Nat × PairData × List RawRow

def coordinateCode (rank : Nat) : LowerOperandCode := (0,rank,(0,0,0,0))

/-- The literal guard prefix, including the same raw head and zero target
in the ordinary endpoint and count occurrences. The numeric norm, not an
effective high-tail cutoff, is the constant in the middle row. -/
def guardRowsCode (p : PairData) : List RawRow :=
  let (head,e,input,output) := p
  [((0,0),e.1,(-1,coordinateCode input) ::
      e.2.map (fun t => (t.1,coordinateCode t.2))),
    ((1,0),-(rawNormCode head : Int),[(1,coordinateCode input)]),
    ((0,0),0,[(-1,coordinateCode output),
      (1,(1,input,(1,0,head,0))),(1,(2,input,(1,0,head,0)))])]

noncomputable def pairBranchesCode (f : Nat → Nat) (p : Args) : List RawBranch :=
  branchesCode f (p.1,p.2.1,guardRowsCode p.2.2.1 ++ p.2.2.2)

noncomputable def originalGuardSnapshot (lam : NONote) (input : Nat)
    (θ : Nat → Nat) : Snapshot :=
  [(0,true),((θ input : Int) - (actualOrdinalNorm lam.1.repr : Int),true),(0,true)]

def OriginalTestAt (test : (Nat → Nat) → Snapshot → Prop) (positive : Bool)
    (θ : Nat → Nat) (values : Snapshot) : Prop :=
  if positive then test θ values else ¬ test θ values

def ExactPairBranchCode : Prop :=
  Primrec guardRowsCode ∧
  (∀ f : Nat → Nat, Computable f → Computable (pairBranchesCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), (pairBranchesCode f p).map Prod.fst = List.range p.2.1) ∧
  ∀ (f : Nat → Nat) (lam : NONote) (e : Expression) (input output rank bound : Nat)
    (testRows : List Row),
    pairBranchesCode f (rank,bound,(rawNoteEncode lam.1,e,input,output),testRows.map encodeRow) =
      (branches f rank bound (AffineCollapseGuardRows.guardRows lam e input output ++ testRows)).map
        encodeBranch

/-- For either original test polarity the original circuit graph and prior
guards remain positive. Only the original test snapshot is passed to the
test. All rows and prior guards see exactly the same updated valuation. -/
def ExactFinitePairLow : Prop :=
  ∀ (f ρ : Nat → Nat) (prior : (Nat → Nat) → Prop)
    (lam : NONote), Order.IsSuccLimit lam.1.repr →
    ∀ (e : Expression) (input output rank bound : Nat) (testRows : List Row)
      (test : (Nat → Nat) → Snapshot → Prop) (positive : Bool),
      (∃ a : Nat, a < bound ∧
        let θ := Function.update ρ rank a
        prior θ ∧ graph f (rawNoteEncode lam.1) e input output θ ∧
          ∃ testValues : Snapshot, actualRows f θ testRows testValues ∧
            OriginalTestAt test positive θ testValues) ↔
      ∃ branch residual,
        branch ∈ branches f rank bound
          (AffineCollapseGuardRows.guardRows lam e input output ++ testRows) ∧
        HitRows branch.2 residual ∧
        let θ := Function.update ρ rank branch.1
        prior θ ∧ ∃ testValues : Snapshot,
          actualRows f θ residual (originalGuardSnapshot lam input θ ++ testValues) ∧
            OriginalTestAt test positive θ testValues

def FullAffineCollapseGuardedLow : Prop := ExactPairBranchCode ∧ ExactFinitePairLow

end LogicLineages.PermittedControl.AffineCollapseGuardedLow

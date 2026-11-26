module
public import LogicLineages.PermittedControl.ActualFiniteSignedNodeBranchTargets
public import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSyntaxLinearTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualZeroClassReplacement (Read liftedReads readSum)
open ActualWeightedReadNormalization (normalizeReads)
open ActualRankedNormalizationSyntax (normalizedTerms)
open ActualFiniteSignedNodeBranch (StaticActive)
open ActualLinearExit (lowerReads table exitRow OriginalSlots replay)
open ActualPreparedSlotAppend (Packet)
open OriginalMatrixLinearRowFormula (testFormula choosePolarity)
open SignedRowGuardedTest (Test)

def lower (top : Nat) (terms : List WeightedOperand) : List WeightedOperand :=
  terms.filter (fun t => decide (t.2.rank < top))

def slope (top : Nat) : List WeightedOperand → Int
  | [] => 0
  | t::ts => if t.2.rank = top then t.1 + slope top ts else slope top ts

def names (i : Nat) : List WeightedOperand → List (Int × NormalForm.Summand)
  | [] => []
  | t::ts => (t.1,.variable i) :: names (i+1) ts

def termsTable (top : Nat) (terms : List WeightedOperand) : List LowerOperand :=
  (lower top terms).map Prod.snd

def termsRow (top : Nat) (constant : Int) (terms : List WeightedOperand) : NormalForm.Row :=
  (constant,(slope top terms,.variable 0) :: names 1 (lower top terms))

noncomputable def packet (top : Nat) (constant : Int) (raw : List WeightedOperand)
    (test : Test) (positive : Bool) : Packet :=
  let terms := normalizedTerms raw
  (termsTable top terms,choosePolarity (testFormula test (termsRow top constant terms)) positive)

def ExactSyntaxOfLinearExit : Prop :=
  ∀ (top : Nat) (constant : Int) (xs : List Read),
    lower top (xs.map Prod.fst) = (lowerReads top xs).map Prod.fst ∧
    termsTable top (xs.map Prod.fst) = table top xs ∧
    termsRow top constant (xs.map Prod.fst) = exitRow top constant xs

/-- True source read domain stays a premise. At other greatest values
only the live normalized tape is replayed, never a discarded raw read. -/
def ExactActualSyntaxLinearTerminal : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (constant : Int)
    (raw : List WeightedOperand) (rs : List Read),
    rs.map Prod.fst = raw →
    (∀ t ∈ raw, t.2.rank ≤ top) →
    liftedReads f ρ rs → ¬ StaticActive top raw →
    ∀ (test : Test) (positive : Bool), test.Admitted →
      let q := packet top constant raw test positive
      ∃ xs : List Read, normalizeReads f ρ rs = some xs ∧
        PreparedInput q.1 q.2 ∧
        (∃ ν : Nat → Nat, PreparedTableTied f top ρ q.1 ν) ∧
        ∀ (ν : Nat → Nat), PreparedTableTied f top ρ q.1 ν →
          OriginalSlots ν (lowerReads top xs) ∧
          (∀ (j : Nat) (hj : j < q.1.length),
            lowerOperandRead f ρ q.1[j] = some (some (ν (j+1)))) ∧
          ((q.2.eval (Function.update ν 0 (ρ top))) ↔ test.atPolarity positive (constant + readSum rs)) ∧
          ∀ z : Nat,
            liftedReads f (Function.update ρ top z) (replay top z xs) ∧
              ((q.2.eval (Function.update ν 0 z)) ↔ test.atPolarity positive (constant + readSum (replay top z xs)))

def FullActualSyntaxLinearTerminal : Prop := ExactSyntaxOfLinearExit ∧ ExactActualSyntaxLinearTerminal

end LogicLineages.PermittedControl.ActualSyntaxLinearTerminal

module
public import LogicLineages.PermittedControl.ActualBoundedSignedRoutesTargets
public import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestCongruenceRoute
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand properOperand encodeWeighted weightedTailCode)
open OriginalMatrixPaidCongruence (Covers paidTerms modular)
open MixedRankResidue (rankSupport)
open SharedRankResidueRow (Layout)
open RankResidueChoices (namedSlots)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSymbolicZeroSuccessor (SyntaxState)
open OriginalMatrixLinearRowFormula (choosePolarity)
open SignedRowGuardedTest (Test)
open SignedRowSliceValue (valueAt)

def lowerRanks (top : Nat) (terms : List WeightedOperand) : List Nat :=
  (rankSupport terms).filter (fun rank => decide (rank < top))

/-- The greatest raw coordinate is the only reserved zero name. Original
raw rank zero remains a positive table name if it is genuinely lower. -/
def layout (top : Nat) (terms : List WeightedOperand) : Layout :=
  (0,top) :: namedSlots (lowerRanks top terms)

def table (top : Nat) (terms : List WeightedOperand) : List LowerOperand :=
  (lowerRanks top terms).map LowerOperand.coordinate

noncomputable def packet (top m : Nat) (s : SyntaxState) (positive : Bool) : Packet :=
  (table top s.terms, choosePolarity (modular (layout top s.terms) m s.constant s.terms) positive)

def modulusMinimum (B m : Nat) (s : SyntaxState) : Nat :=
  s.terms.foldr (fun t n => max (weightedTailCode B m [encodeWeighted t]) n) 0

def LowerModulusSetup (B top m : Nat) (baseline : Nat → Nat) (s : SyntaxState) : Prop :=
  0 < m ∧ (∀ t ∈ s.terms, t.2.rank ≤ top ∧ properOperand t.2) ∧
    ∀ t ∈ s.terms, t.2.rank < top → modulusMinimum B m s ≤ baseline t.2.rank

def SourceCongruence (f ρ : Nat → Nat) (m : Nat) (s : SyntaxState) (positive : Bool) : Prop :=
  ∃ v : Int, valueAt f ρ s.constant s.terms v ∧ (Test.congruence m).atPolarity positive v

def ExactGreatestResidueLayout : Prop :=
  ∀ (top : Nat) (terms : List WeightedOperand),
    ((∀ t ∈ terms, t.2.rank ≤ top) → Covers (layout top terms) terms) ∧
    (∀ slot ∈ layout top terms, slot.1 = 0 ↔ slot.2 = top) ∧
    ∀ slot ∈ layout top terms, slot.1 ≤ (table top terms).length

def ExactGreatestResidueTies : Prop :=
  ∀ (f baseline : Nat → Nat) (top : Nat) (terms : List WeightedOperand),
    (∃ ν, PreparedTableTied f top baseline (table top terms) ν) ∧
    ∀ (ν : Nat → Nat), PreparedTableTied f top baseline (table top terms) ν →
      ∀ (z : Nat) (slot), slot ∈ layout top terms →
        Function.update ν 0 z slot.1 = Function.update baseline top z slot.2

def ExactGreatestCongruenceShape : Prop :=
  ∀ (top m : Nat) (s : SyntaxState) (positive : Bool),
    PreparedInput (packet top m s positive).1 (packet top m s positive).2

def ExactGreatestCongruencePacket : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (baseline : Nat → Nat) (top m : Nat) (s : SyntaxState), LowerModulusSetup B top m baseline s →
      ∀ (z : Nat), modulusMinimum B m s ≤ z → ∀ (positive : Bool),
        let q := packet top m s positive
        PreparedInput q.1 q.2 ∧
        (PacketHolds f baseline top z q ↔
          SourceCongruence f (Function.update baseline top z) m s positive)

def FullActualGreatestCongruenceRoute : Prop :=
  ExactGreatestResidueLayout ∧ ExactGreatestResidueTies ∧ ExactGreatestCongruenceShape ∧
    ExactGreatestCongruencePacket

end LogicLineages.PermittedControl.ActualGreatestCongruenceRoute

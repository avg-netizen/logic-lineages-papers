module
public import LogicLineages.PermittedControl.AffineCollapseGraphCompositionTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGuardRows
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

def zeroTarget : NONote := ⟨.zero, ONote.NF.zero⟩

def affineTerms (e : AffineCollapseGraphComposition.Expression) (input : Nat) :
    List WeightedOperand :=
  (-1,.coordinate input) :: e.2.map (fun t => (t.1,.coordinate t.2))

def collapseTerms (lam : NONote) (input output : Nat) : List WeightedOperand :=
  [(-1,.coordinate output),(1,.ordinary input (.entry 0 lam zeroTarget)),
    (1,.count input lam zeroTarget)]

/-- Original affine equation, actual norm affordability and the original
fixed-head sum of the two fields from the same proper zero-target entry. -/
noncomputable def guardRows (lam : NONote) (e : AffineCollapseGraphComposition.Expression)
    (input output : Nat) : List Row :=
  [(.equalZero,e.1,affineTerms e input),
    (.nonnegative,-(actualOrdinalNorm lam.1.repr : Int),[(1,.coordinate input)]),
    (.equalZero,0,collapseTerms lam input output)]

def trueSnapshot (snapshot : Snapshot) : Prop :=
  ∃ a b c : Int, snapshot = [(a,true),(b,true),(c,true)]

/-- At one given valuation these are exactly the all-true, ordered
snapshots of the original guard, not newly quantified independent fields. -/
def ExactAffineCollapseGuardRows : Prop :=
  ∀ (f : Nat → Nat) (lam : NONote), Order.IsSuccLimit lam.1.repr →
    ∀ (e : AffineCollapseGraphComposition.Expression) (input output : Nat) (θ : Nat → Nat)
      (snapshot : Snapshot),
      (actualRows f θ (guardRows lam e input output) snapshot ∧ trueSnapshot snapshot) ↔
        AffineCollapseGraphComposition.graph f (rawNoteEncode lam.1) e input output θ ∧
          snapshot = [(0,true),((θ input : Int) - (actualOrdinalNorm lam.1.repr : Int),true),(0,true)]

end LogicLineages.PermittedControl.AffineCollapseGuardRows

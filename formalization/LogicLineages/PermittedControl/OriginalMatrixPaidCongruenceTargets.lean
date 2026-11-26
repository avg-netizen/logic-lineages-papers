module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixPaidCongruence
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand encodeWeighted weightedTailCode properOperand orderedReads actualSum)
open MixedRankResidue (rankSupport residueVectorCode)
open SharedRankResidueRow (Layout)
open RankResidueChoices (actualCell)
open MixedRankNamedResidueRow (toVector)
open SignedRowSliceValue (valueAt)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

def paidTerms (B m : Nat) (ρ : Nat → Nat) (ts : List WeightedOperand) : Prop :=
  ∀ t ∈ ts, weightedTailCode B m [encodeWeighted t] ≤ ρ t.2.rank

def Covers (layout : Layout) (ts : List WeightedOperand) : Prop :=
  ∀ t ∈ ts, t.2.rank ∈ layout.map Prod.snd

/-- Names ARE the actual rank indices, including rank zero. No extra
independent named parameter assignment is introduced. -/
def rankLayout (rs : List Row) : Layout :=
  (rankSupport (rs.flatMap (fun r => r.2.2))).map (fun k => (k,k))

noncomputable def modular (layout : Layout) (m : Nat) (c : Int) (ts : List WeightedOperand) :
    NormalForm.Formula :=
  SharedRankResidueRow.formula layout (m,c,ts)

def digitResult (m : Nat) (ρ : Nat → Nat) (layout : Layout) (c : Int) (ts : List WeightedOperand) : Int :=
  c + residueVectorCode (ts.map encodeWeighted) (toVector (actualCell m layout ρ))

/-- Per-original-occurrence paid bounds derive actual reads on true
proper operands (including their actual norm domains) and exact congruence
of the whole signed sum with the existing numeric code. -/
def ExactPaidCongruenceReads : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (layout : Layout) (m : Nat) (c : Int) (ts : List WeightedOperand),
    0 < m → Covers layout ts → (∀ t ∈ ts, properOperand t.2) → paidTerms B m ρ ts →
    ∃ values : List Nat, orderedReads f ρ ts values ∧
      Int.ModEq (m : Int) (c + actualSum ts values) (digitResult m ρ layout c ts)

/-- At a retained true signed value, the existing named formula is
exact even with only the individual term payments. Its false branch
cannot synthesize a successful source value. -/
def ExactPaidCongruenceAtValue : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ ν : Nat → Nat) (layout : Layout) (m : Nat) (c : Int) (ts : List WeightedOperand) (v : Int),
    0 < m → Covers layout ts → paidTerms B m ρ ts →
    (∀ s ∈ layout, ν s.1 = ρ s.2) →
    valueAt f ρ c ts v → ((modular layout m c ts).eval ν ↔ (m : Int) ∣ v)

def paidRow (B : Nat) (ρ : Nat → Nat) (r : Row) : Prop :=
  match r.1 with
  | .congruence m => paidTerms B m ρ r.2.2
  | _ => True

noncomputable def testAt (ρ : Nat → Nat) (layout : Layout) (r : Row) (v : Int) (b : Bool) : Prop :=
  match r.1 with
  | .congruence m =>
      if b then (modular layout m r.2.1 r.2.2).eval ρ else ¬ (modular layout m r.2.1 r.2.2).eval ρ
  | _ => r.1.atPolarity b v

noncomputable def enabledRows (f ρ : Nat → Nat) (layout : Layout) : List Row → Snapshot → Prop
  | [], [] => True
  | r :: rs, (v,b) :: vs =>
      r.1.Admitted ∧ valueAt f ρ r.2.1 r.2.2 v ∧ testAt ρ layout r v b ∧ enabledRows f ρ layout rs vs
  | _, _ => False

/-- Same literal rows, occurrence order and exact values. Replace only
divisibility polarity with the existing compiled modular formula. -/
def ExactPaidCongruenceMatrix : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (rs : List Row), (∀ r ∈ rs, paidRow B ρ r) →
  ∀ snap : Snapshot, actualRows f ρ rs snap ↔ enabledRows f ρ (rankLayout rs) rs snap

def FullOriginalMatrixPaidCongruence : Prop :=
  ExactPaidCongruenceReads ∧ ExactPaidCongruenceAtValue ∧ ExactPaidCongruenceMatrix

end LogicLineages.PermittedControl.OriginalMatrixPaidCongruence

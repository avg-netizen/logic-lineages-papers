module
public import LogicLineages.PermittedControl.StableSortedHighFieldTargets
public import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (WeightedOperand)
open SignedRowGuardedTest (Test sourceTestAt)
open StableSortedHighField (Packet basePacket orderGuard)
open OriginalMatrixLinearRowFormula (choosePolarity)

inductive OrderTest where
  | equalZero | nonnegative | positive

def OrderTest.test : OrderTest → Test
  | .equalZero => .equalZero
  | .nonnegative => .nonnegative
  | .positive => .positive

/-- The exact requested comparison outcome and whether to assert it.
Zero weight is not admitted by the signed-pair theorem. -/
def request (k : OrderTest) (c : Int) : Nat × Bool :=
  match k with
  | .equalZero => (1,true)
  | .nonnegative => (if 0 < c then 0 else 2,false)
  | .positive => (if 0 < c then 2 else 0,true)

def wantedBit (k : OrderTest) (c : Int) (positive : Bool) : Bool :=
  if positive then (request k c).2 else !(request k c).2

def signedTerms (F G : ValueField) (i j : Nat) (c : Int) : List WeightedOperand :=
  [(c,.ordinary i F),(-c,.ordinary j G)]

def source (f ρ : Nat → Nat) (F G : ValueField) (i j : Nat) (c : Int)
    (k : OrderTest) (positive : Bool) : Prop :=
  sourceTestAt f ρ 0 (signedTerms F G i j c) k.test positive

def normCode : ValueField → Nat
  | .iterate _ => 0
  | .entry _ lam _ => rawNormCode (rawNoteEncode lam.1)

/-- Both original domains keep their own literal norm guard; the existing
comparison cutoff is not silently treated as a field reader. -/
def minimum (B : Nat) (F G : ValueField) : Nat :=
  max (highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G))
    (max (normCode F) (normCode G))

/-- Before the greatest raw value is assigned, use the same optional
genuine inverse-comparison operand and bare lower coordinate as the
existing stable sorted packet. Only the comparison is polarity-selected. -/
def strictPacket (F G : ValueField) (lo : Nat) (c : Int)
    (k : OrderTest) (positive : Bool) : Packet :=
  let base := basePacket F G lo (request k c).1
  (base.1 ++ [.coordinate lo],
    .conjunction (orderGuard (base.1.length+1))
      (choosePolarity base.2 (wantedBit k c positive)))

def equalPacket (F G : ValueField) (c : Int) (k : OrderTest) (positive : Bool) : Packet :=
  let answer := sameForm (normalizeShortField F) (normalizeShortField G)
  let base := HighFieldPreparedPacket.constantFormula 0 answer (request k c).1
  ([],choosePolarity base (wantedBit k c positive))

def orientedPacket (F G : ValueField) (i j : Nat) (c : Int) (k : OrderTest)
    (positive : Bool) : Packet :=
  if i < j then strictPacket F G i c k positive
  else if j < i then strictPacket G F j (-c) k positive
  else equalPacket F G c k positive

def ExactSignedPairValue : Prop :=
  ∀ (f ρ : Nat → Nat) (F G : ValueField) (i j u v : Nat) (c : Int), c ≠ 0 →
    LowerOperandActual f ρ (.ordinary i F) u → LowerOperandActual f ρ (.ordinary j G) v →
    ∀ (k : OrderTest) (positive : Bool),
      (source f ρ F G i j c k positive ↔
        if wantedBit k c positive then numericalComparison u v = (request k c).1
        else numericalComparison u v ≠ (request k c).1)

def ExactStrictSignedPair : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, ProperField F → ProperField G →
  ∀ (ρ : Nat → Nat) (lo hi : Nat), lo < hi → minimum B F G ≤ ρ lo →
    ∀ (c : Int), c ≠ 0 → ∀ (k : OrderTest) (positive : Bool),
      let packet := strictPacket F G lo c k positive
      PreparedInput packet.1 packet.2 ∧
      (∀ op ∈ packet.1, op.rank = lo) ∧
      (∃ ν : Nat → Nat, PreparedTableTied f hi ρ packet.1 ν ∧
        ∀ (j : Nat) (hj : j < packet.1.length),
          lowerOperandRead f ρ packet.1[j] = some (some (ν (j+1)))) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f hi ρ packet.1 ν →
        ∀ z : Nat, ρ lo < z →
          let θ := Function.update ρ hi z
          ClosedOrdinaryValueDomain F (θ lo) ∧ ClosedOrdinaryValueDomain G (θ hi) ∧
          (∃ u v : Nat, lowerOperandRead f θ (.ordinary lo F) = some (some u) ∧
            lowerOperandRead f θ (.ordinary hi G) = some (some v)) ∧
          (packet.2.eval (Function.update ν 0 z) ↔ source f θ F G lo hi c k positive)

def ExactEqualRankSignedPair : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, ProperField F → ProperField G →
  ∀ (ρ : Nat → Nat) (rank : Nat) (c : Int), c ≠ 0 → ∀ (k : OrderTest) (positive : Bool),
    let packet := equalPacket F G c k positive
    packet.1 = [] ∧ PreparedInput packet.1 packet.2 ∧
    ∀ (ν : Nat → Nat) (z : Nat), minimum B F G ≤ z →
      let θ := Function.update ρ rank z
      ClosedOrdinaryValueDomain F (θ rank) ∧ ClosedOrdinaryValueDomain G (θ rank) ∧
      (∃ u v : Nat, lowerOperandRead f θ (.ordinary rank F) = some (some u) ∧
        lowerOperandRead f θ (.ordinary rank G) = some (some v)) ∧
      (packet.2.eval (Function.update ν 0 z) ↔ source f θ F G rank rank c k positive)

def ExactReverseSignedPair : Prop :=
  ∀ (f ρ : Nat → Nat) (F G : ValueField) (i j : Nat) (c : Int) (k : OrderTest) (positive : Bool),
    source f ρ G F j i (-c) k positive ↔ source f ρ F G i j c k positive

def orientedMinimum (B : Nat) (F G : ValueField) (i j : Nat) : Nat :=
  if j < i then minimum B G F else minimum B F G

/-- Genuine source orientation: when two ranks differ, the shorter
request packet is indexed by the original lower operand's rank. -/
def ExactOrientedSignedPair : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ F G : ValueField, ProperField F → ProperField G →
  ∀ (ρ : Nat → Nat) (i j : Nat) (c : Int), c ≠ 0 → ∀ (k : OrderTest) (positive : Bool),
    let packet := orientedPacket F G i j c k positive
    let bound := orientedMinimum B F G i j
    (if i = j then True else bound ≤ ρ (min i j)) →
    PreparedInput packet.1 packet.2 ∧
    (∃ ν : Nat → Nat, PreparedTableTied f (max i j) ρ packet.1 ν) ∧
    ∀ (ν : Nat → Nat), PreparedTableTied f (max i j) ρ packet.1 ν →
      ∀ z : Nat, (if i = j then bound ≤ z else ρ (min i j) < z) →
        (packet.2.eval (Function.update ν 0 z) ↔
          source f (Function.update ρ (max i j) z) F G i j c k positive)

def FullActualSignedOrdinaryPairHigh : Prop :=
  ExactSignedPairValue ∧ ExactStrictSignedPair ∧ ExactEqualRankSignedPair ∧ ExactReverseSignedPair ∧
    ExactOrientedSignedPair

end LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh

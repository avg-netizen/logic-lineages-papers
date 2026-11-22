module
public import LogicLineages.PermittedControl.ActualFullValueLabelsTargets
public import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighTargets
public import LogicLineages.PermittedControl.ActualPreparedSlotAppendTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullLabelPairGuards
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualFullValueLabels (Label ActualLabel)
open ActualPreparedSlotAppend (Packet)

abbrev Pair := Label × Label

inductive Answer where
  | less | equal | greater
  deriving DecidableEq

def Answer.code : Answer → Nat
  | .less => 0
  | .equal => 1
  | .greater => 2

def choices : List Answer := [.less,.equal,.greater]

def Pair.maximum (p : Pair) : Nat := max p.1.rank p.2.rank

def Pair.minimum (p : Pair) : Nat := min p.1.rank p.2.rank

def cost (B : Nat) (p : Pair) : Nat :=
  max (ActualSignedOrdinaryPairHigh.minimum B p.1.field p.2.field)
    (ActualSignedOrdinaryPairHigh.minimum B p.2.field p.1.field)

def Ready (B : Nat) (ρ : Nat → Nat) (top : Nat) (p : Pair) : Prop :=
  p.1.rank ≤ top ∧ p.2.rank ≤ top ∧
  ProperField p.1.field ∧ ProperField p.2.field ∧
  (p.1.rank < top → cost B p ≤ ρ p.1.rank) ∧
  (p.2.rank < top → cost B p ≤ ρ p.2.rank)

def PaidUpdate (B : Nat) (ρ : Nat → Nat) (top z : Nat) (p : Pair) : Prop :=
  cost B p ≤ z ∧
  (p.1.rank < top → ρ p.1.rank < z) ∧
  (p.2.rank < top → ρ p.2.rank < z)

def ActualOutcome (f θ : Nat → Nat) (p : Pair) (answer : Answer) : Prop :=
  ∃ u v : Nat, ActualLabel f θ p.1 u ∧ ActualLabel f θ p.2 v ∧
    numericalComparison u v = answer.code

def lowerFormula : Answer → NormalForm.Formula
  | .less => .atom (.nonnegative (-1,[(1,.variable 2),(-1,.variable 1)]))
  | .equal => .conjunction
      (.atom (.nonnegative (0,[(1,.variable 1),(-1,.variable 2)])))
      (.atom (.nonnegative (0,[(1,.variable 2),(-1,.variable 1)])))
  | .greater => .atom (.nonnegative (-1,[(1,.variable 1),(-1,.variable 2)]))

def lowerPacket (p : Pair) (answer : Answer) : Packet :=
  ([.ordinary p.1.rank p.1.field,.ordinary p.2.rank p.2.field],lowerFormula answer)

def topRequest : Answer → Int × ActualSignedOrdinaryPairHigh.OrderTest
  | .less => (-1,.positive)
  | .equal => (1,.equalZero)
  | .greater => (1,.positive)

def topPacket (p : Pair) (a : Answer) : Packet :=
  ActualSignedOrdinaryPairHigh.orientedPacket p.1.field p.2.field
    p.1.rank p.2.rank (topRequest a).1 (topRequest a).2 true

/-- Same distinguished greatest raw slot throughout. A genuinely lower
pair is not evaluated at, or readdressed to, the greatest coordinate. -/
def packet (top : Nat) (p : Pair) (a : Answer) : Packet :=
  if p.maximum < top then lowerPacket p a else topPacket p a

def ExactFullLabelPairGuard : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (top : Nat) (p : Pair), Ready B ρ top p →
    ∀ a : Answer,
      let g := packet top p a
      PreparedInput g.1 g.2 ∧
      (∃ ν : Nat → Nat, PreparedTableTied f top ρ g.1 ν) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top ρ g.1 ν →
        ∀ z : Nat, PaidUpdate B ρ top z p →
          ((g.2.eval (Function.update ν 0 z)) ↔
            ActualOutcome f (Function.update ρ top z) p a)

def ExactActualPairHasOutcome : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (top z : Nat) (p : Pair), Ready B ρ top p → PaidUpdate B ρ top z p →
    ∃ a ∈ choices, ActualOutcome f (Function.update ρ top z) p a

def FullActualFullLabelPairGuards : Prop := ExactFullLabelPairGuard ∧ ExactActualPairHasOutcome

end LogicLineages.PermittedControl.ActualFullLabelPairGuards

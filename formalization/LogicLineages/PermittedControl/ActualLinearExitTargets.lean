module
public import LogicLineages.PermittedControl.ActualWeightedReadNormalizationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualLinearExit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection ActualMixedRowLeadingAnnotations
open ActualZeroClassReplacement ActualWeightedReadNormalization

def lowerReads (zRank : Nat) (xs : List Read) : List Read :=
  xs.filter (fun rd => decide (rd.1.2.rank < zRank))

def slope (zRank : Nat) : List Read → Int
  | [] => 0
  | rd::xs => if rd.1.2.rank = zRank then rd.1.1 + slope zRank xs else slope zRank xs

/-- One positive slot for every retained lower occurrence, in literal
source order and at its original signed coefficient. -/
def namedTerms (name : Nat) : List Read → List (Int × NormalForm.Summand)
  | [] => []
  | rd::xs => (rd.1.1,.variable name) :: namedTerms (name+1) xs

def table (zRank : Nat) (xs : List Read) : List LowerOperand :=
  (lowerReads zRank xs).map (fun rd => rd.1.2)

def exitRow (zRank : Nat) (constant : Int) (xs : List Read) : NormalForm.Row :=
  (constant,(slope zRank xs,.variable 0) :: namedTerms 1 (lowerReads zRank xs))

def replay (zRank z : Nat) : List Read → List Read
  | [] => []
  | rd::xs => (if rd.1.2.rank = zRank then (rd.1,z) else rd) :: replay zRank z xs

/-- The upper slot is unconstrained here. Every used positive slot is
the value of the exact original retained read, not an independent input. -/
def OriginalSlots (ν : Nat → Nat) (rs : List Read) : Prop :=
  ∀ (j : Nat) (hj : j < rs.length), ν (j+1) = rs[j].2

/-- One linear exit of the original normalized row. Uniform replay is for
the live normalized reads only; the raw read sum is recovered only at the
original assignment. Any other source guards have to be preserved by the
caller; no discarded raw field is replayed. -/
def ExactActualLinearExit : Prop :=
  ∀ (f ρ : Nat → Nat) (zRank : Nat) (constant : Int) (raw xs : List Read),
    liftedReads f ρ raw →
    (∀ rd ∈ raw, rd.1.2.rank ≤ zRank) →
    normalizeReads f ρ raw = some xs →
    (¬ ∃ rd ∈ xs, rd.1.1 ≠ 0 ∧ rd.1.2.rank = zRank ∧ NonlinearOperand rd.1.2) →
    let retained := lowerReads zRank xs
    let ops := table zRank xs
    let row := exitRow zRank constant xs
    PreparedInput ops (.atom (.nonnegative row)) ∧
    (∃ ν : Nat → Nat, OriginalSlots ν retained ∧ PreparedTableTied f zRank ρ ops ν) ∧
    (∀ ν : Nat → Nat, PreparedTableTied f zRank ρ ops ν →
      OriginalSlots ν retained ∧
      (∀ (j : Nat) (hj : j < ops.length),
        lowerOperandRead f ρ ops[j] = some (some (ν (j+1)))) ∧
      (∀ z : Nat, PreparedTableTied f zRank (Function.update ρ zRank z) ops
          (Function.update ν 0 z) ∧
        liftedReads f (Function.update ρ zRank z) (replay zRank z xs) ∧
        NormalForm.rowValue row (Function.update ν 0 z) =
          constant + readSum (replay zRank z xs)) ∧
      NormalForm.rowValue row (Function.update ν 0 (ρ zRank)) = constant + readSum raw)

end LogicLineages.PermittedControl.ActualLinearExit

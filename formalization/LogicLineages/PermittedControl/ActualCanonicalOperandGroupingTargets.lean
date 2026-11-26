module
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets
public import Mathlib.Data.List.Dedup

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
open PreparedProjection MixedSameRankResidue ActualZeroClassReplacement
open ActualWeightedReadNormalization ActualReadChargeIteration

/-- Explicit first occurrence order: List.dedup retains the last occurrence,
so reverse both before and after using it. -/
def firstKeys {α : Type} [DecidableEq α] (keys : List α) : List α :=
  keys.reverse.dedup.reverse

def signedWeight {α : Type} [DecidableEq α] (terms : List (Int × α)) (key : α) : Int :=
  (terms.map (fun t => if t.2 = key then t.1 else 0)).sum

def groupTape {α : Type} [DecidableEq α] (terms : List (Int × α)) : List (Int × α) :=
  ((firstKeys (terms.map Prod.snd)).map (fun key => (signedWeight terms key,key))).filter
    (fun t => decide (t.1 ≠ 0))

abbrev RawTerm := Int × LowerOperandCode

def encodeTerm (t : WeightedOperand) : RawTerm := (t.1,t.2.code)

def groupRaw (terms : List RawTerm) : List RawTerm := groupTape terms

/-- This layer does not compute the guard. It takes an already available
result of checking every source occurrence, including zero weights. -/
def groupCheckedRaw (allReadsHit : Bool) (terms : List RawTerm) : Option (List RawTerm) :=
  if allReadsHit then some (groupRaw terms) else none

noncomputable def groupTyped (terms : List WeightedOperand) : List WeightedOperand := by
  classical
  exact groupTape terms

/-- All original occurrences are checked first. The ordered surviving
keys are then read at their original rank using the genuine reader. -/
noncomputable def normalizeCanonical (f ρ : Nat → Nat) (xs : List Read) : Option (List Read) :=
  if checkedReads f ρ xs then
    let weights := groupedWeights xs
    ((groupTyped (xs.map Prod.fst)).map Prod.snd).mapM (readAtWeight f ρ weights)
  else none

def ExactOperandEncoding : Prop :=
  Function.Injective LowerOperand.code ∧ Function.Injective encodeTerm

def ExactCanonicalTape : Prop :=
  (∀ (terms : List WeightedOperand),
      (groupTyped terms).map encodeTerm = groupRaw (terms.map encodeTerm)) ∧
  (∀ (terms : List WeightedOperand), ((groupTyped terms).map Prod.snd).Nodup) ∧
  ∀ (xs : List Read) (w : Int) (key : LowerOperand),
    (w,key) ∈ groupTyped (xs.map Prod.fst) ↔
      w = groupedWeights xs key ∧ key ∈ (groupedWeights xs).support

def ExactCanonicalReads : Prop :=
  ∀ (f ρ : Nat → Nat) (xs : List Read),
    (normalizeCanonical f ρ xs = none ↔ ¬ liftedReads f ρ xs) ∧
    ∀ old : List Read, normalizeReads f ρ xs = some old →
      ∃ out : List Read, normalizeCanonical f ρ xs = some out ∧
        out.Perm old ∧ out.map Prod.fst = groupTyped (xs.map Prod.fst) ∧
        liftedReads f ρ out ∧ readSum out = readSum xs

def ExactCanonicalCharge : Prop :=
  ∀ (r : Nat) (c : Int) (out old : List Read), out.Perm old →
    groupedWeights out = groupedWeights old ∧
    stateCharge r ⟨c,out⟩ = stateCharge r ⟨c,old⟩

def FullActualCanonicalOperandGrouping : Prop :=
  ExactOperandEncoding ∧ ExactCanonicalTape ∧ ExactCanonicalReads ∧ ExactCanonicalCharge

end LogicLineages.PermittedControl.ActualCanonicalOperandGrouping

module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsTargets
open NormalForm InactivePhiRows

def ExactOccurrencePartition : Prop := ∀ (r : Row) (mask : List Bool),
  mask.length = r.2.length → ∀ ν : Nat → Nat,
    rowValue r ν = rowValue (remaining r mask) ν + rowValue (dropped r mask) ν

def GuardedValuePreservation : Prop := ∀ (r : Row) (i : Nat) (mask : List Bool),
  mask ∈ masks i r → ∀ ν : Nat → Nat,
    (guard r mask).eval ν → rowValue (remaining r mask) ν = rowValue r ν

/-- Coverage is proved from actual inactive provenance, not assumed as an
external exhaustive-cases hypothesis. Complete equal-input classes touching
the eliminated name can be deleted together. -/
def FiniteInactiveCoverage : Prop := ∀ (r : Row), PlainPhiDominance.isPlain r = true →
  ∀ (i : Nat) (ν : Nat → Nat), PlainPhiDominance.active i r ν = false →
    ∃ mask ∈ masks i r, (guard r mask).eval ν

def LiteralLinearOutput : Prop := ∀ (i : Nat) (a : Atom),
  LinearRows.isLinear i (compileAtom i a) = true

def ActualInactiveAtom : Prop := ∀ (i : Nat) (a : Atom),
  PlainPhiDominance.isPlain a.row = true → ∀ ν : Nat → Nat,
    PlainPhiDominance.active i a.row ν = false →
      ((compileAtom i a).eval ν ↔ a.eval ν)

/-- Both children retain only literal original occurrence values. -/
def LiteralRetainedOccurrences : Prop := ∀ (r : Row) (mask : List Bool),
  (∀ a ∈ (remaining r mask).2, a ∈ r.2) ∧
    (∀ a ∈ (dropped r mask).2, a ∈ r.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsTargets

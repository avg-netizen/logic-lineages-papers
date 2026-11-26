module
public import LogicLineages.StandardControlCurrent.MixedCancellationDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellationTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm MixedCancellation

def Enumeration : Prop := ∀ n bs, bs ∈ masks n ↔ bs.length=n

def Partition : Prop := ∀ r bs, bs.length=r.2.length → ∀ ν,
  rowValue r ν = rowValue (retained r bs) ν +
    ((selected r bs).map (fun a => a.1*(a.2.term.value ν : Int))).sum

/-- Every actual equal-value class has a literal mask; zero sum is not assumed. -/
def ClassCoverage : Prop := ∀ (r : Row) (anchor : Int × Summand), anchor ∈ r.2 → ∀ ν,
  ∃ bs ∈ masks r.2.length,
    selected r bs = r.2.filter (fun a => decide (a.2.term.value ν=anchor.2.term.value ν)) ∧
    anchor ∈ selected r bs ∧ (equalGuard r bs).eval ν

def Cancellation : Prop := ∀ r bs, bs.length=r.2.length → coefficientSum r bs=0 → ∀ ν,
  (equalGuard r bs).eval ν → rowValue (retained r bs) ν=rowValue r ν

/-- Entire actual original domain remains inside the hole, even under negation. -/
def GuardedSemantics : Prop := ∀ c a bs ν,
  (step c a bs).2.eval ν ↔ (before c a bs).eval ν

/-- Count includes BOTH the equality guard and all original domain guards.
No assertion compares the initial unguarded formula to a guarded branch. -/
def Progress : Prop := ∀ c a bs,
  ((step c a bs).1=true → matrixNodes (step c a bs).2 < matrixNodes (before c a bs)) ∧
  ((step c a bs).1=false → (step c a bs).2=before c a bs) ∧
  ((step c a bs).1=true ↔ enabled a.row bs=true)

def Support : Prop := ∀ c a bs j,
  j ∈ (step c a bs).2.variables → j ∈ (before c a bs).variables

def Full : Prop := Enumeration ∧ Partition ∧ ClassCoverage ∧ Cancellation ∧
  GuardedSemantics ∧ Progress ∧ Support
end LogicLineages.StandardControlCurrent.MixedCancellationTargets

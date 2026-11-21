module
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FiniteStripRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

/-- Actual signed-formula substitution, retaining the existing Boolean tree.
The rightmost read is substituted first; repeated names have last-read priority
in the corresponding valuation. Collector-produced names will be distinct. -/
def foldFormula (reads : List (Nat × Nat)) (p : NormalForm.Formula) : NormalForm.Formula :=
  reads.foldr (fun r q => BoundedRows.substitute r.1 r.2 q) p

def foldCode (reads : List (Nat × Nat)) (code : Nat) : Nat :=
  reads.foldr (fun r c => BoundedRows.Code.formula r.1 r.2 c) code

def foldValuation (reads : List (Nat × Nat)) (ν : Nat → Nat) : Nat → Nat :=
  reads.foldl (fun μ r => Function.update μ r.1 r.2) ν

def FoldCodeExact : Prop :=
  Primrec₂ foldCode ∧ ∀ (reads : List (Nat × Nat)) (p : NormalForm.Formula), foldCode reads p.encode = (foldFormula reads p).encode

def FoldActual : Prop :=
  ∀ (reads : List (Nat × Nat)) (p : NormalForm.Formula) (ν : Nat → Nat), (foldFormula reads p).eval ν ↔ p.eval (foldValuation reads ν)

def FoldSupport : Prop :=
  ∀ (reads : List (Nat × Nat)) (p : NormalForm.Formula) (i : Nat), i ∈ (foldFormula reads p).variables ↔
    i ∉ reads.map Prod.fst ∧ i ∈ p.variables

def FoldPlain : Prop :=
  ∀ (reads : List (Nat × Nat)) (p : NormalForm.Formula), PlainPreparedFormula p → PlainPreparedFormula (foldFormula reads p)

/-- Arbitrary dual slot valuations, not independently chosen nonlinear values.
The caller must pay agreement on every ORIGINAL live name after actual updates. -/
def FoldDualValuation : Prop :=
  ∀ (reads : List (Nat × Nat)) (p : NormalForm.Formula) (ν μ : Nat → Nat),
    (∀ i ∈ p.variables, foldValuation reads ν i = μ i) →
    ((foldFormula reads p).eval ν ↔ p.eval μ)

/-- Reconstructed candidate after executor loss, NOT reuse of historical #731.
No field-read totality, finite rank coverage, source guard rejection, or QE. -/
def FullFold : Prop :=
  FoldCodeExact ∧ FoldActual ∧ FoldSupport ∧ FoldPlain ∧ FoldDualValuation
end LogicLineages.PermittedControl.FiniteStripRecovery

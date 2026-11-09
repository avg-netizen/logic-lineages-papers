module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsTargets
open BlockRows

def ActualOriginalRowEmbedding : Prop := ∀ (r : NormalForm.Row) (ν : Nat → Nat),
  rowValue (Row.ofOriginal r) ν = NormalForm.rowValue r ν
def ActualOriginalFormulaEmbedding : Prop := ∀ (p : NormalForm.Formula) (ν : Nat → Nat),
  (Formula.ofOriginal p).eval ν ↔ p.eval ν
def ActualInitialBlockIndependence : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  ParametersIndependent bound (Formula.ofOriginal p)
def ActualExpandedCompilation : Prop := ∀ (p : Formula) (ν : Nat → Nat),
  p.compile.eval ν ↔ p.eval ν
def ActualSourceSubstitution : Prop :=
  (∀ (r : Row) (i : Nat) (replacement : Term) (ν : Nat → Nat),
    rowValue (r.substitute i replacement) ν =
      rowValue r (Function.update ν i (replacement.value ν))) ∧
  (∀ (p : Formula) (i : Nat) (replacement : Term) (ν : Nat → Nat),
    (p.substitute i replacement).eval ν ↔ p.eval (Function.update ν i (replacement.value ν)))

/-- Current-source occurrences only: no normalization/cancellation count is
substituted for this exact literal filter. -/
def ExactRemainingOccurrences : Prop := ∀ (r : Row) (i : Nat) (replacement : Term),
  (r.substitute i replacement).2 = r.2.filter (fun a => a.2.name != i)
def ExactOriginalNameSupport : Prop := ∀ (p : Formula) (i : Nat) (replacement : Term) (j : Nat),
  j ∈ (p.substitute i replacement).variables ↔
    (j ∈ p.variables ∧ j ≠ i) ∨ (i ∈ p.variables ∧ j ∈ replacement.variables)
def WholeBlockParameterIndependence : Prop :=
  ∀ (bound : List Nat) (p : Formula) (i : Nat) (replacement : Term),
    ParametersIndependent bound p → (∀ j ∈ bound, j ∉ replacement.variables) →
      ParametersIndependent bound (p.substitute i replacement)

/-- Original signed domains stay at the original guarded atom's Boolean
position, including every zero/cancelled source occurrence. They are never
replaced by a new global-domain convention for the rewritten rows. -/
def ExactOriginalGuardedDomains : Prop :=
  ∀ (a : NormalForm.Atom) (i : Nat) (replacement : Term) (ν : Nat → Nat),
    ((Formula.ofOriginal (NormalForm.guardedAtom a)).substitute i replacement).compile.eval ν ↔
      NormalForm.rowMeaningful a.row (Function.update ν i (replacement.value ν)) ∧
        a.eval (Function.update ν i (replacement.value ν))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsTargets

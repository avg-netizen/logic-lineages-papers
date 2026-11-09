module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationTargets
open WholeBoundInitialization

def LiteralOccurrencePartition : Prop := ∀ (bound : List Nat) (r : NormalForm.Row),
  (row bound r).2 = r.2.filter (fun a => bound.contains a.2.name)

def LiteralParameterSupport : Prop := ∀ (bound : List Nat) (r : NormalForm.Row) (j : Nat),
  j ∈ (row bound r).parameters ↔ j ∈ NormalForm.rowVariables r ∧ j ∉ bound

def LiteralRowSemantics : Prop := ∀ (bound : List Nat) (r : NormalForm.Row) (ν : Nat → Nat),
  BlockRows.rowValue (row bound r) ν = NormalForm.rowValue r ν

def ActualFormulaSemantics : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula) (ν : Nat → Nat),
  («initialize» bound p).eval ν ↔ p.eval ν

def WholeBoundParameterIndependence : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  BlockRows.ParametersIndependent bound («initialize» bound p)

def ExactOriginalNameSupport : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula) (j : Nat),
  j ∈ («initialize» bound p).variables ↔ j ∈ p.variables

def ActualAllowedTest : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  ZeroShift p → TiedLinear.allowed bound («initialize» bound p) = true

def HFreeInitialization : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  ZeroShift p → PlainBlockSplit.formulaHFree («initialize» bound p) = true

def ExactPrefixSemantics : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula) (ν : Nat → Nat),
  PlainBlockSplit.existsPrefix ν bound («initialize» bound p) ↔ NormalForm.existsPrefix ν bound p

/-- This is the paid concrete typed projector applied to the actual initializer.
No separate initializer invariant or supplied solver is an endpoint premise. -/
def ActualInitializedProjection : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  bound.Nodup → ZeroShift p → ∀ ν : Nat → Nat,
    ((project bound p).eval ν ↔ NormalForm.existsPrefix ν bound p)

def OriginalProjectedNameSupport : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  bound.Nodup → ZeroShift p → ∀ j ∈ (project bound p).variables,
    j ∉ bound ∧ j ∈ p.variables

def HFreeProjectedOutput : Prop := ∀ (bound : List Nat) (p : NormalForm.Formula),
  bound.Nodup → ZeroShift p → PlainBlockSplit.matrixHFree (project bound p) = true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationTargets

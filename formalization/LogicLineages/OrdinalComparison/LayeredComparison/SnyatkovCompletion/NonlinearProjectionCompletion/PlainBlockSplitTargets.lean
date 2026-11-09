module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitTargets
open BlockRows PlainBlockSplit

def LiteralTieSemantics : Prop := ∀ (p : Formula) (i j : Nat),
  i ∉ p.parameters → ∀ ν : Nat → Nat,
    ((rename i j p).eval ν ↔ p.eval (Function.update ν i (ν j)))

def StrictOriginalBoundDecrease : Prop := ∀ (bound : List Nat) (p : Formula) (s : State),
  s ∈ branches bound p → s.1.length < bound.length

def ActualOneStepProjection : Prop := ∀ (bound : List Nat) (p : Formula),
  bound.Nodup → bound ≠ [] → TiedLinear.allowed bound p = true →
  ParametersIndependent bound p → ∀ ν : Nat → Nat,
    (existsPrefix ν bound p ↔ ∃ s ∈ branches bound p, existsPrefix ν s.1 s.2)

def WholeBlockStateClosure : Prop := ∀ (bound : List Nat) (p : Formula),
  TiedLinear.allowed bound p = true → ParametersIndependent bound p →
  ∀ s ∈ branches bound p,
    TiedLinear.allowed s.1 s.2 = true ∧ ParametersIndependent s.1 s.2

def OriginalBranchNameSupport : Prop := ∀ (bound : List Nat) (p : Formula),
  TiedLinear.allowed bound p = true → ParametersIndependent bound p →
  ∀ s ∈ branches bound p, ∀ j ∈ s.2.variables, j ∈ p.variables ∨ j ∈ bound

def HFreeBranchClosure : Prop := ∀ (bound : List Nat) (p : Formula),
  TiedLinear.allowed bound p = true → ParametersIndependent bound p → formulaHFree p = true →
  ∀ s ∈ branches bound p, formulaHFree s.2 = true

/-- Complete typed uniform block projection on the actual source-graph state
class. The program/effectivity contract is separate and remains unpaid. -/
def ActualUniformBlockProjection : Prop := ∀ (bound : List Nat) (p : Formula),
  bound.Nodup → TiedLinear.allowed bound p = true → ParametersIndependent bound p →
  ∀ ν : Nat → Nat, ((project bound p).eval ν ↔ existsPrefix ν bound p)

def OriginalOutputNameSupport : Prop := ∀ (bound : List Nat) (p : Formula),
  bound.Nodup → TiedLinear.allowed bound p = true → ParametersIndependent bound p →
  ∀ j ∈ (project bound p).variables, j ∉ bound ∧ j ∈ p.variables

def HFreeOutputClosure : Prop := ∀ (bound : List Nat) (p : Formula),
  bound.Nodup → TiedLinear.allowed bound p = true → ParametersIndependent bound p →
  formulaHFree p = true → matrixHFree (project bound p) = true

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitTargets

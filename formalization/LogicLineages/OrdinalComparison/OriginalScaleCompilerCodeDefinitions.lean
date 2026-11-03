module
public import LogicLineages.OrdinalComparison.NumericUnaryChainDefinitions
public import LogicLineages.OrdinalComparison.NumericCarrierDataDefinitions
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeDefinitions
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode
open NumericUnaryChain

/-- Actual caller type and positive curried-ground arity are checked before
literal saturation. The supplied source and all assigned fields remain. -/
def callerCode (Γ : List Nat) (σ src : Nat) : Option RawOperator := do
  let τ ← SyntaxCode.check Γ src
  if τ=σ then
    let r ← TrackedSourceInspectionCode.arityCode σ
    if r=0 then none else
      let u ← DefaultSourceAssignment.assignmentCode Γ src
      pure ([],NumericCarrierData.saturateSource (r-1) src,NumericCarrierData.saturateVector (r-1) u)
  else none

def paidCode (b : Nat) (xs : List RawOperator) (caller : RawOperator) : List RawOperator :=
  (List.replicate (2^b) xs).flatten ++ List.replicate (2^b) caller

def gapCode (b : Nat) (xs : List RawOperator) (c : Nat) : Nat :=
  2^b * (c-3*xs.length-3)-1

/-- One original-scale literal list and one actual final unary abstraction. -/
def compileScaleCode (Γ : List Nat) (σ src b : Nat) (xs : List RawOperator) :
    Option (List Nat×Nat×List Nat) := do
  let caller ← callerCode Γ σ src
  NumericUnaryChain.compileCode Γ (paidCode b xs caller)
end LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode

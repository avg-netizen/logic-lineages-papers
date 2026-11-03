module
public import LogicLineages.OrdinalComparison.UnitEliminationTreeCodeDefinitions
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeDefinitions
public import LogicLineages.OrdinalComparison.SelectedBinderCodeDefinitions
public import LogicLineages.OrdinalComparison.OneUnitCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode
open UnitEliminationTreeCode

/-- Literal finite-fuel compiler. Every branch uses the actual numeric source
checker, selector, permutation, one-unit coefficients and ground-block payload.
Recursive source codes can grow; only fuel is the termination measure. -/
def buildCode : Nat → List Nat → Nat → Option Nat
  | 0,_,_ => none
  | fuel+1,Γ,src => do
    let τ ← SyntaxCode.check Γ src
    match UnitContextSelectionCode.selectCode Γ with
    | none => pure (leafCode (Encodable.encode (UnitGroundBlockCode.buildCode Γ.length τ src)))
    | some (left,σ,right) =>
      let a := SelectedBinderCode.sourceCode 0 left.length src
      let d ← OneUnitCode.compileCode (left++right) σ a
      let q ← buildCode fuel (left++right) (OneUnitCode.firstCode σ a)
      if d.2.2 then pure (freeCode (Encodable.encode (left,right,σ,d.1)) q)
      else
        let r ← buildCode fuel (left++right) (OneUnitCode.secondCode σ a)
        pure (activeCode (Encodable.encode (left,right,σ,OneUnitCode.coefficientCode τ,
          d.1,d.2.1,OneUnitCode.constantCode τ d.2.1)) q r)

def compileCode (Γ : List Nat) (src : Nat) : Option Nat := buildCode (Γ.length+1) Γ src
noncomputable def realizedCompileCode (Γ : List Nat) (src : Nat) : Option Nat :=
  (compileCode Γ src).map UnitEliminationTreeCode.realizeCode
end LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode

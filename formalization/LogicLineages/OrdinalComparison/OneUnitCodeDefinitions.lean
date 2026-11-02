module
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesDefinitions
public import LogicLineages.OrdinalComparison.SourceOneUnitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnitCode

def unusedCode (src : Nat) : Nat := 8*Nat.pair 0 (ContextInsertionCode.sourceCode 0 1 src)+6
def firstCode (σ src : Nat) : Nat := 8*Nat.pair σ src+6
def secondCode (σ src : Nat) : Nat := firstCode σ (unusedCode src)
def multiplierCode (σ : Nat) (v : List Nat) : Nat :=
  2^(SyntaxCode.typeLevel σ+1) * (v.map OrdinalSyntax.partialSize).sum
def dataCode (d : OneUnit.Data) : Nat×Nat×Bool := (d.d,d.d',d.free)

def compileCode (Γ : List Nat) (σ src : Nat) : Option (Nat×Nat×Bool) := do
  let h ← DefaultSourceAssignment.assignmentCode (σ::Γ) src
  let h' ← DefaultSourceAssignment.assignmentCode (σ::Γ) (unusedCode src)
  pure (multiplierCode σ h,multiplierCode σ h',OrdinalSyntax.headFree (h.getD 0 0))

def coefficientCode (τ : Nat) : Nat := 2*(SyntaxCode.typeLevel τ+1)+1
def constantCode (τ d' : Nat) : Nat :=
  4*(2*(SyntaxCode.typeLevel τ+1))*d'+2*(SyntaxCode.typeLevel τ+1)
end LogicLineages.OrdinalComparison.Source.OneUnitCode

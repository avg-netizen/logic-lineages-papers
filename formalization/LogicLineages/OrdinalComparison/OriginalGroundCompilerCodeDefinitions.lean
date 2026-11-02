module
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeDefinitions
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeDefinitions
public import LogicLineages.OrdinalComparison.NumericAccountDataDefinitions
public import LogicLineages.OrdinalComparison.OriginalGroundDataConstructionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode

/-- The two actual carrier-private functional names remain separate. Every
record retains its literal source and complete assigned vector. -/
def packRecords (σ : Nat) (rs : List Nat) : List NumericUnaryChain.RawOperator :=
  rs.map (fun r => ([σ,σ],SourceAnnotationCode.operatorSource r,SourceAnnotationCode.operatorVector r))

/-- Uniform raw original-source compiler. It constructs data only: certificates
in the correctness theorem are not consumed by this algorithm. The body is
checked ground and tracked-active; the caller's exact type and positive arity
are checked by the actual scale compiler. Original b is never enlarged. -/
def compileCode (Γ : List Nat) (σ body caller : Nat) :
    Option ((List Nat×Nat×List Nat)×Nat×Nat) := do
  if SyntaxCode.check (σ::Γ) body = some 0 then
    if TrackedSourceInspectionCode.occursCode 0 body then
      let (_,rs,c) ← NumericAccountData.sourceAccountCode (σ::Γ) body
      let b ← OriginalBudgetCode.budgetCode (σ::Γ) body
      let xs := packRecords σ rs
      let out ← OriginalScaleCompilerCode.compileScaleCode Γ σ caller b xs
      pure (out,b,OriginalScaleCompilerCode.gapCode b xs c)
    else none
  else none
end LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode

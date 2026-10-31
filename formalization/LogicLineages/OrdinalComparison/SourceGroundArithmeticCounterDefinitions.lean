module
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerDefinitions
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter
open OriginalDomain GroundEquivalence PrimitiveLowering BooleanCompiler

/-- The two observed scalars share the original names; b is weakened only to
pass beneath a's newly bound observation wire. -/
def counter {Γ} (strict : Bool) (a b : Input Γ .ground) : Program Γ :=
  .observation a (.observation (ScopedDAG.renameInput (Renaming.weaken Γ .ground) b)
    (.matrix (.snoc .nil (if strict then .le 1 0 else .lt 1 0))
      ![.var (.there .here),.var .here] 0))

noncomputable def RawQuery {Γ} (strict : Bool) (ρ : Variable Γ .ground → Nat)
    (a b : Input Γ .ground) : Prop :=
  if strict then
    SourceCollisionCompletion.rawScalar (valuation (UnitObservation.substitution ρ)) a.term <
      SourceCollisionCompletion.rawScalar (valuation (UnitObservation.substitution ρ)) b.term
  else
    SourceCollisionCompletion.rawScalar (valuation (UnitObservation.substitution ρ)) a.term ≤
      SourceCollisionCompletion.rawScalar (valuation (UnitObservation.substitution ρ)) b.term
end LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter

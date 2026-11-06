module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceTargets
open Source Source.ForwardTranslation Source.SourceClasses

/-- Actual original canonical terms, without compilation-success or polynomial
head premises. Every internal subterm and binder is covered by the level bound.
The full counterexample is closed; its original variables remain positive and
its fresh graph nodes are natural. This is a reduction, not a decision theorem. -/
def ActualLevelTwoCounterexamples : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
    InternalLevelBound 2 a → InternalLevelBound 2 b → ∀ mode : Nat,
    ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level) (p : Pair.Package),
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
      SourceCode.compile (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = some p ∧
      (Pair.Closed p ↔ ∃ ρ : OrdinalComponent Γ → Nat,
        (∀ c, 0 < ρ c) ∧ ¬SourceCode.sourceRelation mode av bv ρ)

def ActualNumericProgram : Prop := Primrec SourceCode.compile
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceTargets

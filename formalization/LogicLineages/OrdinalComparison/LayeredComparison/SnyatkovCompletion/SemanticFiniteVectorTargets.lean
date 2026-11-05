module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorTargets
open SemanticFiniteVector Source Source.ForwardTranslation RecursorFreeVector

def CompleteVectorDecision : Prop := ∀ (ι : Type) (index : ι → Nat) (n mode k l : Nat)
  (a : CompiledVector ι k) (b : CompiledVector ι l),
  SemanticFiniteScalar.finiteHeads a.scalar → SemanticFiniteScalar.finiteHeads b.scalar →
  ∃ answer, SemanticFiniteVector.Code.decideVectors (n,mode,a.syntaxCode index,b.syntaxCode index) = some answer ∧
    ((∀ ν : Nat → Nat, (∀ i < n, 0 < ν i) → vectorRelation mode a b (fun i => ν (index i))) ↔
      answer = true)

/-- No scalar-compilation success premise: the independently stated semantic
finiteSource condition ensures success through actual canonical extraction. -/
def ActualSourceDecision : Prop := ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ τ (a b : OriginalTerm Γ τ), finiteSource a → finiteSource b → ∀ mode,
  ∃ (av bv : OrdinalVector Γ τ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
    ∃ answer,
      SemanticFiniteVector.Code.decideSource (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = some answer ∧
      ((∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) → sourceRelation mode av bv ρ) ↔ answer = true)

def RecursorFreePasses : Prop := ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ τ (e : OriginalTerm Γ τ), SourceClasses.recursorFree e = true → finiteSource e

def ActualNumericPrograms : Prop := Computable SemanticFiniteVector.Code.decideVectors ∧
  Computable SemanticFiniteVector.Code.decideSource
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorTargets

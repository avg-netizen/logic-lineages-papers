module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorTargets
open RecursorFreeVector Source Source.ForwardTranslation CommonLayerSyntax

def ExactFormula : Prop := ∀ n mode a b,
  Code.formula n mode a.encode b.encode = (formula n mode a b).encode ∧
  ∀ ν, (formula n mode a b).eval ν ↔
    ((∀ i < n, 0 < ν i) → scalarRelation mode (a.value ν) (b.value ν))

def ActualVectorDecision : Prop := ∀ (ι : Type) (index : ι → Nat) (n mode k l : Nat)
  (a : CompiledVector ι k) (b : CompiledVector ι l) ta tb,
  FiniteCoefficientBase.compile index a.scalar = some ta →
  FiniteCoefficientBase.compile index b.scalar = some tb →
  ∃ answer, Code.decideVectors (n,mode,a.syntaxCode index,b.syntaxCode index) = some answer ∧
    ((∀ ν : Nat → Nat, (∀ i < n, 0 < ν i) → vectorRelation mode a b (fun i => ν (index i))) ↔
      answer = true)

def ActualSourceRelation : Prop := ∀ (Γ : List Ty) (k l mode : Nat)
  (a : OrdinalVector Γ k) (b : OrdinalVector Γ l)
  (ca : CompiledVector (OrdinalComponent Γ) k) (cb : CompiledVector (OrdinalComponent Γ) l),
  compileVector a = some ca → compileVector b = some cb →
  ∀ ρ, vectorRelation mode ca cb ρ ↔ sourceRelation mode a b ρ

/-- The actual printed recursor-free subcase, not the arbitrary semantically
finite-coefficient class. Original terms have the SAME type and ground free
context, with no bound on their internal types, binders, or assignment length. -/
def ActualRecursorFreeDecision : Prop := ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ τ (a b : OriginalTerm Γ τ), SourceClasses.recursorFree a = true →
  SourceClasses.recursorFree b = true → ∀ mode,
  ∃ (av bv : OrdinalVector Γ τ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
    ∃ answer,
      Code.decideSource (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = some answer ∧
      ((∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) → sourceRelation mode av bv ρ) ↔ answer = true)

def ActualNumericPrograms : Prop := Computable Code.decideVectors ∧ Computable Code.decideSource
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorTargets

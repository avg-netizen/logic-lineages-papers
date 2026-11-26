module

public import LogicLineages.NativeModule.PersistentMarking.FiniteDomainFoundation

@[expose] public section

namespace LogicLineages.PersistentMarking.FiniteDomainFoundationTargets
open Spine NameBridge DecisionPorts FiniteDomainFoundation

def ExprEquality : Prop := ∀ q r, exprEq q r = true ↔ q=r
def ArgsEquality : Prop := ∀ qs rs, argsEq qs rs = true ↔ qs=rs

def ObservationDedup : Prop := ∀ xs : List Expr,
  (∀ q, q ∈ distinctObservations xs ↔ q ∈ xs) ∧ (distinctObservations xs).Pairwise (· ≠ ·)
def ContextDedup : Prop := ∀ xs : List Context,
  (∀ Γ, Γ ∈ distinctContexts xs ↔ Γ ∈ xs) ∧ (distinctContexts xs).Pairwise (· ≠ ·)

def PrefixExact : Prop := ∀ σ domains τ,
  (domains,τ) ∈ fullPrefixes σ ↔ domains ≠ [] ∧ ArrowPrefix domains τ = σ
def PrefixProper : Prop := ∀ σ domains τ,
  (domains,τ) ∈ fullPrefixes σ →
  typeSize τ < typeSize σ ∧ ∀ ρ, ρ ∈ domains → typeSize ρ < typeSize σ
def PrefixDistinct : Prop := ∀ σ, (fullPrefixes σ).Pairwise (· ≠ ·)

def VectorExact : Prop := ∀ bounds code, code ∈ vectors bounds ↔ Fits bounds code
def VectorDistinct : Prop := ∀ bounds, (vectors bounds).Pairwise (· ≠ ·)
def VectorCoordinates : Prop := ∀ bounds code,
  Fits bounds code ↔ bounds.length = code.length ∧
    ∀ (i n v : Nat), bounds[i]? = some n → code[i]? = some v → v<n

def EmptyAndZero : Prop := vectors [] = [[]] ∧ ∀ ns, vectors (0::ns) = []
end LogicLineages.PersistentMarking.FiniteDomainFoundationTargets

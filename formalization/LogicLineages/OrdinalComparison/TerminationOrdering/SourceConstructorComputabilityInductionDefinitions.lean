module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityInduction
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedFiniteUniverse
open OrdinaryArithmeticQuotient PositiveArithmeticOperators SourceConstructorComputability RankedPrecedenceCertificate

/-- Every later coordinate remains universal at the fixed head rank and base
multiset. The permutation is on literal actual quotient codes, not an observer. -/
def NumberedAt {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty) (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)) (rank : Fin n → Fin n)
    (head : Nat) (values : List Nat) (k : Nat) : Prop :=
  ∀ (f : Head (Fin n)) (tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types),
    headRank rank f = head → (ArgumentValues ctx base).Perm values →
    InUniverse ctx.1.1 ctx.1.2 (.numbered k f tau base types extras) →
    ArgumentsC context ctx scalar base → ArgumentsC context ctx scalar extras →
    TermC context ctx scalar (.numbered k f tau base types extras)

def OrdinaryAt {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty) (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)) (rank : Fin n → Fin n)
    (head : Nat) (values : List Nat) : Prop :=
  ∀ (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f)),
    headRank rank f = head → (ArgumentValues ctx base).Perm values →
    InUniverse ctx.1.1 ctx.1.2 (.ordinary f base) → ArgumentsC context ctx scalar base →
    TermC context ctx scalar (.ordinary f base)

def AtBase {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty) (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)) (rank : Fin n → Fin n)
    (head : Nat) (values : List Nat) : Prop :=
  (∀ k : Nat, NumberedAt arity Gamma context ctx scalar rank head values k) ∧
    OrdinaryAt arity Gamma context ctx scalar rank head values
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityInduction

module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.Logic.Godel.GodelBetaFunction

@[expose] public section

/-! Ordinary first-order arithmetic only: the four function symbols below and
built-in equality. In particular there is no beta, program, checker, path or
semantic-predicate symbol. The two beta code components are separate variables;
no arithmetic representation of pairing is presupposed. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic

open FirstOrder Language

inductive FunctionSymbol : Nat → Type where
  | zero : FunctionSymbol 0
  | succ : FunctionSymbol 1
  | add : FunctionSymbol 2
  | mul : FunctionSymbol 2

def arithmeticLanguage : Language := ⟨FunctionSymbol, fun _ => Empty⟩

instance naturalStructure : arithmeticLanguage.Structure Nat where
  funMap := fun {_} f v => match f with
    | .zero => 0
    | .succ => Nat.succ (v 0)
    | .add => v 0 + v 1
    | .mul => v 0 * v 1
  RelMap := fun r => nomatch r

abbrev Term (α : Type) := arithmeticLanguage.Term α
abbrev Formula (α : Type) := arithmeticLanguage.Formula α

def zeroTerm {α : Type} : Term α := .func .zero Fin.elim0
def succTerm {α : Type} (t : Term α) : Term α :=
  FirstOrder.Language.Functions.apply₁ FunctionSymbol.succ t
def addTerm {α : Type} (s t : Term α) : Term α :=
  FirstOrder.Language.Functions.apply₂ FunctionSymbol.add s t
def mulTerm {α : Type} (s t : Term α) : Term α :=
  FirstOrder.Language.Functions.apply₂ FunctionSymbol.mul s t

/-- Bound variables 0 and 1 denote the quotient and strict-bound witness.
The body says a = q*((i+1)*b+1)+r and r+succ(d)=((i+1)*b+1). -/
def betaBody {α : Type} (a b i r : Term α) :
    arithmeticLanguage.BoundedFormula α 2 :=
  let lift : Term α → Term (α ⊕ Fin 2) := fun t => t.relabel Sum.inl
  let modulus := succTerm (mulTerm (succTerm (lift i)) (lift b))
  ((lift a).bdEqual (addTerm (mulTerm (.var (.inr 0)) modulus) (lift r))) ⊓
    ((addTerm (lift r) (succTerm (.var (.inr 1)))).bdEqual modulus)

def betaFormula {α : Type} (a b i r : Term α) : Formula α :=
  (betaBody a b i r).exs

/-- Free variables in order: first code component, second code component,
index, sequence entry. -/
def betaGraph : Formula (Fin 4) :=
  betaFormula (.var 0) (.var 1) (.var 2) (.var 3)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic

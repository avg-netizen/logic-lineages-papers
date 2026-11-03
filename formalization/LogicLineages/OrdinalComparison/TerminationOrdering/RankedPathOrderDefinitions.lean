module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedTreeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrder
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree

mutual
/-- Recursive multiset equality on ranked trees. This is the unordered
first-order algebra equality, not literal argument-position equality. -/
inductive Equal (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :
    Tree Symbol arity Gamma → Tree Symbol arity Gamma → Prop where
  | var (v : Variable Gamma .ground) : Equal Symbol arity Gamma (.var v) (.var v)
  | node (f : Symbol) (ss ts : Fin (arity f) → Tree Symbol arity Gamma)
      (matched : List (Tree Symbol arity Gamma)) :
      (List.ofFn ts).Perm matched → EqualMatch Symbol arity Gamma (List.ofFn ss) matched →
      Equal Symbol arity Gamma (.node f ss) (.node f ts)
inductive EqualMatch (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :
    List (Tree Symbol arity Gamma) → List (Tree Symbol arity Gamma) → Prop where
  | nil : EqualMatch Symbol arity Gamma [] []
  | cons (s t : Tree Symbol arity Gamma) (ss ts : List (Tree Symbol arity Gamma)) :
      Equal Symbol arity Gamma s t → EqualMatch Symbol arity Gamma ss ts →
      EqualMatch Symbol arity Gamma (s::ss) (t::ts)
end

mutual
/-- Standard multiset recursive path ordering. The subterm clause uses its
weak closure; precedence and multiset clauses also dominate ALL target
arguments. The independent definition has no marked auxiliary syntax,
special-application function, Boolean interpretation or original derivation. -/
inductive Greater (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) : Tree Symbol arity Gamma → Tree Symbol arity Gamma → Prop where
  | subterm (f : Symbol) (ss : Fin (arity f) → Tree Symbol arity Gamma)
      (i : Fin (arity f)) (t : Tree Symbol arity Gamma) :
      Weak Symbol arity Gamma above (ss i) t →
      Greater Symbol arity Gamma above (.node f ss) t
  | precedence (f g : Symbol) (ss : Fin (arity f) → Tree Symbol arity Gamma)
      (ts : Fin (arity g) → Tree Symbol arity Gamma) :
      above f g → (∀ i,Greater Symbol arity Gamma above (.node f ss) (ts i)) →
      Greater Symbol arity Gamma above (.node f ss) (.node g ts)
  | multiset (f : Symbol) (ss ts : Fin (arity f) → Tree Symbol arity Gamma) :
      MultisetGreater Symbol arity Gamma above (List.ofFn ss) (List.ofFn ts) →
      (∀ i,Greater Symbol arity Gamma above (.node f ss) (ts i)) →
      Greater Symbol arity Gamma above (.node f ss) (.node f ts)
inductive Weak (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) : Tree Symbol arity Gamma → Tree Symbol arity Gamma → Prop where
  | equal (s t : Tree Symbol arity Gamma) : Equal Symbol arity Gamma s t → Weak Symbol arity Gamma above s t
  | greater (s t : Tree Symbol arity Gamma) : Greater Symbol arity Gamma above s t → Weak Symbol arity Gamma above s t
inductive MultisetGreater (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) : List (Tree Symbol arity Gamma) → List (Tree Symbol arity Gamma) → Prop where
  | replace (ss ts kept retained removed inserted : List (Tree Symbol arity Gamma)) :
      ss.Perm (kept++removed) → ts.Perm (retained++inserted) → removed≠[] →
      EqualMatch Symbol arity Gamma kept retained → Replacement Symbol arity Gamma above removed inserted →
      MultisetGreater Symbol arity Gamma above ss ts
inductive Replacement (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (above : Symbol → Symbol → Prop) : List (Tree Symbol arity Gamma) → List (Tree Symbol arity Gamma) → Prop where
  | nil (removed : List (Tree Symbol arity Gamma)) : Replacement Symbol arity Gamma above removed []
  | cons (removed : List (Tree Symbol arity Gamma)) (s t : Tree Symbol arity Gamma)
      (rest : List (Tree Symbol arity Gamma)) :
      s∈removed → Greater Symbol arity Gamma above s t → Replacement Symbol arity Gamma above removed rest →
      Replacement Symbol arity Gamma above removed (t::rest)
end

def GreaterEqual {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Tree Symbol arity Gamma) : Prop :=
  Equal Symbol arity Gamma s t ∨ Greater Symbol arity Gamma above s t

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrder

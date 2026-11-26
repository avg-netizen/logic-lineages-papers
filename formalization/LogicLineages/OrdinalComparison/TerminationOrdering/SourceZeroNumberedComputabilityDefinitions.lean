module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceNeutralExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputability
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientPaths

/-- Literal typed canonical codes of the immediate arguments, in their original order. -/
def argumentCodes {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    {Gamma types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) : List (Ty × Nat) :=
  (argumentList args).map (fun p => (p.1, representativeCode symbols S p))

/-- The numbered label, with no observation depth or finite approximant. -/
def numberedLabel {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Option Nat :=
  match q.2 with
  | .numbered k _ _ _ _ _ => some k
  | _ => none

/-- Immediate base and extra members of an actual numbered term. -/
def numberedMembers {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) : List (Ty × Nat) :=
  match q.2 with
  | .numbered _ _ _ base _ extras => argumentCodes symbols S base ++ argumentCodes symbols S extras
  | _ => []

/-- A bookkeeping witness for replacing one literal member by one actual quotient edge.
This is not a replacement for the original term relation. -/
def OneMemberReplacement (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    (source target : List (Ty × Nat)) : Prop :=
  ∃ (kept : List (Ty × Nat)) (sigma : Ty) (x y : Nat),
    source.Perm (kept ++ [(sigma,x)]) ∧ target.Perm (kept ++ [(sigma,y)]) ∧
    QuotientEdge n arity symbols S above Gamma x y
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputability

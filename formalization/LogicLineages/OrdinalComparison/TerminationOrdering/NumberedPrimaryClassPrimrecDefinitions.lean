module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassDefinitions
public import Mathlib.Logic.Function.Iterate
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrec
open Source NumberedRewriteReduction NumberedAuxiliaryDecoding NumberedExchangeNeighborhood

/-- The original seed and candidate list, with all original repetitions retained. -/
def vertexList {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q : Packed Symbol arity Gamma) : List (Packed Symbol arity Gamma) :=
  q :: classCandidates symbols S q

/-- One finite reachability step using the original exchange test. -/
def step {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (vertices reached : List (Packed Symbol arity Gamma)) :
    List (Packed Symbol arity Gamma) :=
  reached ++ vertices.filter
    (fun r => reached.any (fun a => exchangeTest symbols S a r))

/-- Exactly the supplied number of list reachability steps from the original seed. -/
def reachableList {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q : Packed Symbol arity Gamma) (fuel : Nat) : List (Packed Symbol arity Gamma) :=
  (step symbols S (vertexList symbols S q))^[fuel] [q]

/-- A sufficient finite cutoff computable directly from the original candidate list. -/
def primaryList {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q : Packed Symbol arity Gamma) : List (Packed Symbol arity Gamma) :=
  reachableList symbols S q (vertexList symbols S q).length

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrec

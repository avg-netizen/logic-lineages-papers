module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClass
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryDecoding NumberedExchangeNeighborhood

local instance {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty} : DecidableEq (Packed Symbol arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

def vertices {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) : Finset (Packed Symbol arity Gamma) :=
  insert q (classCandidates symbols S q).toFinset

def reachStep {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma)
    (A : Finset (Packed Symbol arity Gamma)) : Finset (Packed Symbol arity Gamma) :=
  A ∪ (vertices symbols S q).filter (fun r => ∃ a∈A,exchangeTest symbols S a r=true)

def reachable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) : Nat → Finset (Packed Symbol arity Gamma)
  | 0 => {q}
  | n+1 => reachStep symbols S q (reachable symbols S q n)

def primaryClass {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q : Packed Symbol arity Gamma) : Finset (Packed Symbol arity Gamma) :=
  reachable symbols S q (vertices symbols S q).card

def primaryTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q r : Packed Symbol arity Gamma) : Bool :=
  decide (r∈primaryClass symbols S q)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClass

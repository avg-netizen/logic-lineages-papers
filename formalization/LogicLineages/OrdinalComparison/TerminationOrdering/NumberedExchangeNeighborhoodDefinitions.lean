module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhood
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedPrimaryExchange

def argumentsFromList {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (types : List Ty) (values : List (Packed Symbol arity Gamma)) : Option (AuxArguments Symbol arity Gamma types) :=
  match types,values with
  | [],[] => some .nil
  | sigma::types,value::values =>
    if h : value.1=sigma then
      (argumentsFromList types values).map (fun rest => .cons (h ▸ value.2) rest)
    else none
  | _,_ => none

def ordinaryNeighbors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (f : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f)) : List (AuxTerm Symbol arity Gamma (headResult f)) :=
  if HeadInWindow arity symbols S f then
    (headWindow arity symbols S).flatMap fun g =>
      if RecursiveComparison.headEquivalent f g then
        if h : headResult g=headResult f then
          (argumentList base).permutations.filterMap fun values =>
            (argumentsFromList (headArguments arity g) values).map (fun target => h ▸ AuxTerm.ordinary g target)
        else []
      else []
  else []

def numberedNeighbors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (k : Nat) (f : Head Symbol) (tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f)) (types : List Ty)
    (extras : AuxArguments Symbol arity Gamma types) : List (AuxTerm Symbol arity Gamma tau) :=
  if HeadInWindow arity symbols S f then
    (headWindow arity symbols S).flatMap fun g =>
      if RecursiveComparison.headEquivalent f g then
        (argumentList base).permutations.filterMap fun values =>
          (argumentsFromList (headArguments arity g) values).map (fun target => AuxTerm.numbered k g tau target types extras)
      else []
  else []

mutual
def neighbors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (symbols : List Symbol) (S : List Ty) : AuxTerm Symbol arity Gamma tau → List (AuxTerm Symbol arity Gamma tau)
  | .var _ | .bottom _ => []
  | .lam body => (neighbors symbols S body).map AuxTerm.lam
  | .app q a => (neighbors symbols S q).map (fun r => .app r a) ++ (neighbors symbols S a).map (fun b => .app q b)
  | .ordinary f base => ordinaryNeighbors symbols S f base ++ (argumentNeighbors symbols S base).map (AuxTerm.ordinary f)
  | .numbered k f tau base types extras => numberedNeighbors symbols S k f tau base types extras ++
      (argumentNeighbors symbols S base).map (fun target => .numbered k f tau target types extras) ++
      (argumentNeighbors symbols S extras).map (fun target => .numbered k f tau base types target)

def argumentNeighbors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma types : List Ty}
    (symbols : List Symbol) (S : List Ty) : AuxArguments Symbol arity Gamma types → List (AuxArguments Symbol arity Gamma types)
  | .nil => []
  | .cons q rest => (neighbors symbols S q).map (fun r => .cons r rest) ++
      (argumentNeighbors symbols S rest).map (fun target => .cons q target)
end

def exchangeTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (q r : Packed Symbol arity Gamma) : Bool :=
  letI : DecidableEq (Packed Symbol arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq
  decide (r∈(neighbors symbols S q.2).map (fun a => (⟨q.1,a⟩ : Packed Symbol arity Gamma)))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhood

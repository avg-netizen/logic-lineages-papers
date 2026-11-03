module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCode
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
  NumberedAuxiliaryEnumeration NumberedFiniteUniverse

/-- Preserve the explicit type and term code of every argument-list entry.
Malformed argument spines fail instead of being treated as empty lists. -/
def argumentEntries {Symbol : Type} : Code Symbol → Option (List (Ty × Code Symbol))
  | .argumentsNil => some []
  | .argumentsCons tau q rest =>
    (argumentEntries rest).map (fun entries => (tau, q) :: entries)
  | _ => none

/-- The literal permutation test on two successfully extracted argument lists. -/
def argumentPermutation {Symbol : Type} [DecidableEq Symbol]
    (base target : Code Symbol) : Bool :=
  match argumentEntries base, argumentEntries target with
  | some source, some result => decide (source.Perm result)
  | _, _ => false

/-- The common root-head guard from the original finite neighborhood.
The target uses actual enumeration membership, without a closure premise. -/
def headMove {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (f : HeadCode Symbol) (base : Code Symbol)
    (g : HeadCode Symbol) (target : Code Symbol) : Bool :=
  decide (HeadInWindow arity symbols S (decodeHead f)) &&
    decide (g ∈ sourceHeads arity symbols S) &&
    decide (RecursiveComparison.headEquivalent (decodeHead f) (decodeHead g)) &&
    argumentPermutation base target

/-- Structural membership checker for the original one-step neighborhood.
All unchanged annotations and siblings are compared literally. -/
def codeExchange {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) : Code Symbol → Code Symbol → Bool
  | .lam sigma q, .lam rho r =>
    decide (sigma = rho) && codeExchange arity symbols S q r
  | .app sigma q a, .app rho r b =>
    decide (sigma = rho) &&
      ((decide (a = b) && codeExchange arity symbols S q r) ||
        (decide (q = r) && codeExchange arity symbols S a b))
  | .ordinary f base, .ordinary g target =>
    (headMove arity symbols S f base g target &&
      decide (headResult (decodeHead g) = headResult (decodeHead f))) ||
      (decide (f = g) && codeExchange arity symbols S base target)
  | .numbered k f tau base types extras,
      .numbered l g upsilon target otherTypes otherExtras =>
    decide (k = l ∧ tau = upsilon ∧ types = otherTypes) &&
      ((decide (extras = otherExtras) &&
          headMove arity symbols S f base g target) ||
        (decide (f = g ∧ extras = otherExtras) &&
          codeExchange arity symbols S base target) ||
        (decide (f = g ∧ base = target) &&
          codeExchange arity symbols S extras otherExtras))
  | .argumentsCons sigma q rest, .argumentsCons rho r target =>
    decide (sigma = rho) &&
      ((decide (rest = target) && codeExchange arity symbols S q r) ||
        (decide (q = r) && codeExchange arity symbols S rest target))
  | _, _ => false

/-- Typed packed inputs must also have equal result types. -/
def packedCodeExchange {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (q r : Ty × Code Symbol) : Bool :=
  decide (q.1 = r.1) && codeExchange arity symbols S q.2 r.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCode

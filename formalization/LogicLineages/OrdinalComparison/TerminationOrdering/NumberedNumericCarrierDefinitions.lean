module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrier
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedNumericDecoding

mutual
def universeTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (symbols : List Symbol) (S : List Ty) : AuxTerm Symbol arity Gamma tau → Bool
  | .var _ => decide (tau∈S)
  | @AuxTerm.lam _ _ _ sigma _ body => decide (tau∈S) && decide (sigma∈S) && universeTest symbols S body
  | .app q a => decide (tau∈S) && universeTest symbols S q && universeTest symbols S a
  | .bottom _ => decide (tau∈S)
  | .ordinary f base => decide (tau∈S) && decide (HeadInWindow arity symbols S f) && argumentsUniverseTest symbols S base
  | .numbered _ f _ base _ extras => decide (tau∈S) && decide (HeadInWindow arity symbols S f) &&
      argumentsUniverseTest symbols S base && argumentsUniverseTest symbols S extras

def argumentsUniverseTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma types : List Ty}
    (symbols : List Symbol) (S : List Ty) : AuxArguments Symbol arity Gamma types → Bool
  | .nil => true
  | .cons q rest => universeTest symbols S q && argumentsUniverseTest symbols S rest
end

def decodeUniverse (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) : Option (Packed (Fin n) arity Gamma) :=
  (decodePackedNumber n arity Gamma value).filter (fun q => universeTest symbols S q.2)

def rawCarrierTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) : Bool :=
  (decodeUniverse n arity symbols S Gamma value).isSome

def canonicalCarrierTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) : Bool :=
  match decodeUniverse n arity symbols S Gamma value with
  | none => false
  | some q => decide (representativeCode symbols S q=value)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrier

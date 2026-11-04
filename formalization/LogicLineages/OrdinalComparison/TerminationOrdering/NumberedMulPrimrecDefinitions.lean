module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrec
open Source Source.SourceMarkedSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedFiniteUniverse
open NumberedMultisetCertificate NumberedMultisetNumeric NumberedExchangeCode

/-- Strict argument-spine extraction followed by the original packed numeric decoder.
The order and repetitions of every successfully decoded argument are retained. -/
def argumentValues (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (code : Code (Fin n)) : Option (List (Packed (Fin n) arity Gamma)) :=
  (argumentEntries code).bind (fun entries =>
    decodePackedNumbers n arity Gamma
      (entries.map (fun entry => Nat.pair (typeNumber entry.1) (codeNumber entry.2))))

/-- Structural execution of the original typed Mul certificate decision. The
source must have a positive label, the target must be ordinary, and only the
original target head/window and base-list certificate conditions are tested. -/
def codeMulTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (source target : Code (Fin n))
    (certificate : MultisetCertificate n arity Gamma) : Bool :=
  match source, target with
  | .numbered (_ + 1) f tau base _ _, .ordinary g targetBase =>
    decide (tau = headResult (decodeHead g) ∧
      RecursiveComparison.headEquivalent (decodeHead f) (decodeHead g) ∧
      HeadInWindow arity symbols S (decodeHead g)) &&
      match argumentValues n arity Gamma base, argumentValues n arity Gamma targetBase with
      | some sourceValues, some targetValues => multisetTest sourceValues targetValues certificate
      | _, _ => false
  | _, _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrec

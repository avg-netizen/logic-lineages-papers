module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMul
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedFiniteUniverse NumberedExchangeCode NumberedUniformMultiset

/-- The original Mul root and base-list conditions on structural data. Strict
argument extraction retains every occurrence and ignores no malformed spine. -/
def rawMulTest {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (source target : Code (Fin n)) (certificate : RawCertificate n) : Bool :=
  match source, target with
  | .numbered (_ + 1) f tau base _ _, .ordinary g targetBase =>
    decide (tau = headResult (decodeHead g) ∧
      RecursiveComparison.headEquivalent (decodeHead f) (decodeHead g) ∧
      HeadInWindow arity symbols S (decodeHead g)) &&
      match argumentEntries base, argumentEntries targetBase with
      | some sourceValues, some targetValues => rawMultisetTest sourceValues targetValues certificate
      | _, _ => false
  | _, _ => false

/-- The unguarded original Mul-selector leaf. Only its original certificate
decoder depends on Gamma; the focus supplies the typed endpoint data. -/
def mulTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (source target : Code (Fin n)) (certificate : Nat) : Bool :=
  (decodeRawCertificate n arity Gamma certificate).any
    (fun data => rawMulTest arity symbols S source target data)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMul

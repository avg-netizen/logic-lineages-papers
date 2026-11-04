module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperation
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
  NumberedFiniteUniverse NumberedCopyCertificate NumberedSelfApplication

abbrev Table (n : Nat) := Fin n → Fin n → Bool

/-- Literal structural Copy operation. The existing positive-label, result-type,
head-precedence and target-window guards are unchanged. -/
def copyCode {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (table : Table n) (g : HeadCode (Fin n)) : Code (Fin n) → Option (Code (Fin n))
  | .numbered (k + 1) f tau base types extras =>
    if tau = headResult (decodeHead g) ∧
        RecursiveComparison.headAbove (tableAbove table) (decodeHead f) (decodeHead g) ∧
        HeadInWindow arity symbols S (decodeHead g) then
      some (.ordinary g
        (selfCode (k, f, base, types, extras) (headArguments arity (decodeHead g))))
    else none
  | _ => none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperation

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrec
open Source

/-- Same actual shared windows/table input as the accepted positive-path checker.
Its standard function/product Primcodable presentation is explicit; no claim
identifies it with a differently selected Encodable context-code instance. -/
abbrev Parameters (n : Nat) := (List (Fin n) × List Ty) × (Fin n → Fin n → Bool)

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrec

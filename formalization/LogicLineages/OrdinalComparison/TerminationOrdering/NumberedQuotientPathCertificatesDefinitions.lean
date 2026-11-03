module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificates
open Source NumberedCopyCertificate NumberedMultisetNumeric NumberedQuotientPaths NumberedNumericQuotientEdge

/-- Each entry is its literal next vertex and the actual certificate for that edge. -/
abbrev EdgeEntry := Nat × Nat

def pathTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) : Nat → Nat → List EdgeEntry → Bool
  | x,y,[] => decide (x=y)
  | x,y,(z,certificate)::rest => numericEdgeTest n arity symbols S Gamma table x z certificate &&
      pathTest n arity symbols S Gamma table z y rest

def pathCertificateNumber (entries : List EdgeEntry) : Nat := numbersNumber (entries.map (fun e => Nat.pair e.1 e.2))

def decodePathCertificate (value : Nat) : Option (List EdgeEntry) := (decodeNumbers value).map (List.map Nat.unpair)

def positivePathTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y certificate : Nat) : Bool :=
  match decodePathCertificate certificate with
  | none => false
  | some [] => false
  | some (entry::rest) => pathTest n arity symbols S Gamma table x y (entry::rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificates

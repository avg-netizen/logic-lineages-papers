module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificate
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedMarkCertificate

/-- A removed occurrence index and its literal finite marking label. -/
abbrev MarkWitness := Nat × Nat

def replacementTest {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (removed : List (Packed (Fin n) arity Gamma)) : List (Packed (Fin n) arity Gamma) → List MarkWitness → Bool
  | [],[] => true
  | q::rest,(index,label)::witnesses =>
    match removed[index]? with
    | none => false
    | some s =>
      letI : DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq
      decide (markTarget label s=some q) && replacementTest removed rest witnesses
  | _,_ => false

structure MultisetCertificate (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) where
  kept : List (Packed (Fin n) arity Gamma)
  removed : List (Packed (Fin n) arity Gamma)
  inserted : List (Packed (Fin n) arity Gamma)
  witnesses : List MarkWitness

def multisetTest {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (source target : List (Packed (Fin n) arity Gamma)) (certificate : MultisetCertificate n arity Gamma) : Bool :=
  letI : DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq
  decide (source.Perm (certificate.kept++certificate.removed) ∧
    target.Perm (certificate.kept++certificate.inserted) ∧ certificate.removed≠[]) &&
    replacementTest certificate.removed certificate.inserted certificate.witnesses

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificate

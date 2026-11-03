module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificate
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedMultisetCertificate

inductive MulInstance (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) :
    Packed (Fin n) arity Gamma → Packed (Fin n) arity Gamma → Prop where
  | mul (k : Nat) (f g : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
      (target : AuxArguments (Fin n) arity Gamma (headArguments arity g)) :
      RecursiveComparison.headEquivalent f g → HeadInWindow arity symbols S g →
      PrimitiveMultiset (argumentList base) (argumentList target) →
      MulInstance n arity symbols S Gamma
        ⟨headResult g,.numbered (k+1) f (headResult g) base types extras⟩ ⟨headResult g,.ordinary g target⟩

def mulCertificateTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) (certificate : MultisetCertificate n arity Gamma) : Bool :=
  match q,r with
  | ⟨_,.numbered (_+1) f tau base _ _⟩,⟨_,.ordinary g target⟩ =>
    decide (tau=headResult g ∧ RecursiveComparison.headEquivalent f g ∧ HeadInWindow arity symbols S g) &&
      multisetTest (argumentList base) (argumentList target) certificate
  | _,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificate

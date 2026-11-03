module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericMulProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificate
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction

inductive DirectRule where
  | put (label : Nat)
  | abstraction
  | beta
  | bottom

def directTarget {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty) : DirectRule → Packed (Fin n) arity Gamma → Option (Packed (Fin n) arity Gamma)
  | .put label,⟨_,.ordinary f base⟩ => some ⟨headResult f,.numbered label f (headResult f) base [] .nil⟩
  | .abstraction,⟨_,.numbered (k+1) f (.arrow sigma tau) base types extras⟩ =>
      some ⟨.arrow sigma tau,.lam (openNumbered k f sigma tau base types extras)⟩
  | .beta,⟨_,.app (.lam body) a⟩ => some ⟨_,NumberedRewriteSyntax.substitute body (singleSubstitution a)⟩
  | .bottom,⟨_,.bottom _⟩ => none
  | .bottom,⟨tau,_⟩ => some ⟨tau,.bottom tau⟩
  | _,_ => none

inductive DirectInstance (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    DirectRule → Packed (Fin n) arity Gamma → Packed (Fin n) arity Gamma → Prop where
  | put (label : Nat) (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f)) :
      DirectInstance n arity Gamma (.put label) ⟨headResult f,.ordinary f base⟩ ⟨headResult f,.numbered label f (headResult f) base [] .nil⟩
  | abstraction (k : Nat) (f : Head (Fin n)) (sigma tau : Ty) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) :
      DirectInstance n arity Gamma .abstraction ⟨.arrow sigma tau,.numbered (k+1) f (.arrow sigma tau) base types extras⟩
        ⟨.arrow sigma tau,.lam (openNumbered k f sigma tau base types extras)⟩
  | beta (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma::Gamma) tau) (a : AuxTerm (Fin n) arity Gamma sigma) :
      DirectInstance n arity Gamma .beta ⟨tau,.app (.lam body) a⟩ ⟨tau,NumberedRewriteSyntax.substitute body (singleSubstitution a)⟩
  | bottom (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau) : q≠.bottom tau →
      DirectInstance n arity Gamma .bottom ⟨tau,q⟩ ⟨tau,.bottom tau⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificate

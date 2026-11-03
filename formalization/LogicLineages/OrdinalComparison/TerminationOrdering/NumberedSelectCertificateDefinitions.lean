module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificate
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction

def selectTarget {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty) (types : List Ty) (index : Nat)
    (q : Packed (Fin n) arity Gamma) : Option (Packed (Fin n) arity Gamma) :=
  match q with
  | ⟨tau,.numbered (k+1) f _ base extraTypes extras⟩ =>
    match (argumentList base++argumentList extras)[index]? with
    | none => none
    | some ⟨sigma,selected⟩ =>
      if ht : sigma=arrows types tau then
        some ⟨tau,applyArguments (ht ▸ selected) (selfArguments k f base extraTypes extras types)⟩
      else none
  | _ => none

inductive SelectInstance (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Packed (Fin n) arity Gamma → Packed (Fin n) arity Gamma → Prop where
  | select (k : Nat) (f : Head (Fin n)) (tau : Ty) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (extraTypes : List Ty) (extras : AuxArguments (Fin n) arity Gamma extraTypes) (types : List Ty)
      (selected : AuxTerm (Fin n) arity Gamma (arrows types tau)) :
      (⟨arrows types tau,selected⟩ : Packed (Fin n) arity Gamma)∈argumentList base++argumentList extras →
      SelectInstance n arity Gamma ⟨tau,.numbered (k+1) f tau base extraTypes extras⟩
        ⟨tau,applyArguments selected (selfArguments k f base extraTypes extras types)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificate

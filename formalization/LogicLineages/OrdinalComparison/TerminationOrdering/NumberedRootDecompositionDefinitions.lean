module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepContextsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecomposition
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedDirectCertificate NumberedSelectCertificate NumberedMulCertificate NumberedStepContexts

/-- Exactly the actual non-context rules. Copy retains an arbitrary actual precedence relation. -/
inductive RootInstance (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (Gamma : List Ty) : Packed (Fin n) arity Gamma → Packed (Fin n) arity Gamma → Prop where
  | direct (rule : DirectRule) (q r : Packed (Fin n) arity Gamma) :
      DirectInstance n arity Gamma rule q r → RootInstance n arity symbols S above Gamma q r
  | select (q r : Packed (Fin n) arity Gamma) :
      SelectInstance n arity Gamma q r → RootInstance n arity symbols S above Gamma q r
  | mul (q r : Packed (Fin n) arity Gamma) :
      MulInstance n arity symbols S Gamma q r → RootInstance n arity symbols S above Gamma q r
  | copy (k : Nat) (f g : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) :
      RecursiveComparison.headAbove above f g → HeadInWindow arity symbols S g →
      RootInstance n arity symbols S above Gamma
        ⟨headResult g,.numbered (k+1) f (headResult g) base types extras⟩
        ⟨headResult g,.ordinary g (selfArguments k f base types extras (headArguments arity g))⟩

def TermDecomposition {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) {Gamma : List Ty} {tau : Ty} (q r : AuxTerm (Fin n) arity Gamma tau) : Prop :=
  ∃ (holeGamma : List Ty) (holeType : Ty) (a b : AuxTerm (Fin n) arity holeGamma holeType)
    (context : TermContext n arity holeGamma holeType Gamma tau),
    q=plug context a ∧ r=plug context b ∧ RootInstance n arity symbols S above holeGamma ⟨holeType,a⟩ ⟨holeType,b⟩

def ArgumentDecomposition {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) {Gamma types : List Ty} (q r : AuxArguments (Fin n) arity Gamma types) : Prop :=
  ∃ (holeGamma : List Ty) (holeType : Ty) (a b : AuxTerm (Fin n) arity holeGamma holeType)
    (context : ArgumentContext n arity holeGamma holeType Gamma types),
    q=plugArguments context a ∧ r=plugArguments context b ∧ RootInstance n arity symbols S above holeGamma ⟨holeType,a⟩ ⟨holeType,b⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecomposition

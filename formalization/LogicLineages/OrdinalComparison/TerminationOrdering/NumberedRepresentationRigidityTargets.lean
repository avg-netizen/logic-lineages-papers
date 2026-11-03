module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPositiveMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceUnmarkedDefinitions

@[expose] public section
/-! Exact syntactic suppliers for numbered derivation simulation. An unmarked
source has a unique representation; arbitrary marked-source representations
are deliberately NOT identified. The marking clauses expose the literal
partial function equation needed by the actual primitive multiset rule.
No source transitivity, equivalence quotient, termination or oracle premise.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentationRigidityTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

def ActualUnmarkedRepresentation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (n : Nat) (Gamma : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau)
    (Q : AuxTerm Symbol arity Gamma tau), SourceUnmarked.Unmarked Symbol arity Gamma q →
    Represents Symbol arity n Gamma tau q Q → Q=canonical 0 q

def ActualUnmarkedArguments : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (n : Nat) (Gamma types : List Ty) (args : Arguments Symbol arity Gamma types)
    (values : AuxArguments Symbol arity Gamma types),
    SourceUnmarked.ArgumentsUnmarked Symbol arity Gamma args →
    ArgumentsRepresent Symbol arity n Gamma types args values → values=canonicalArguments 0 args

def ActualFiniteMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (n : Nat) (Gamma : List Ty) (tau : Ty) (q r : MarkedTerm Symbol arity Gamma tau),
    RecursiveComparison.strictMark q=some r → ∀ Q : AuxTerm Symbol arity Gamma tau,
    Represents Symbol arity (n+1) Gamma tau q Q →
    ∃ R, finiteMark n Q=some R ∧ Represents Symbol arity n Gamma tau r R

def ActualPrimitiveMark : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (n : Nat) (Gamma : List Ty) (tau : Ty) (q r : MarkedTerm Symbol arity Gamma tau),
    RecursiveComparison.strictMark q=some r → ∀ Q : AuxTerm Symbol arity Gamma tau,
    Represents Symbol arity (n+1) Gamma tau q Q →
    ∃ R, PrimitiveMark Symbol arity Gamma ⟨tau,Q⟩ ⟨tau,R⟩ ∧
      Represents Symbol arity n Gamma tau r R

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentationRigidityTargets

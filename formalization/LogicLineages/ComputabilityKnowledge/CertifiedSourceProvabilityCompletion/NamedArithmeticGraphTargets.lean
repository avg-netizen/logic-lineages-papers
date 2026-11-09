module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraphDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraph.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof

/-- A genuine internal derivation at EVERY actual subtree occurrence, with
arbitrary source terms, including U, and all original free parameters. -/
def CallSatisfiesGraph : Prop :=
  ∀ (n : Nat) (p : Program n) (arity : Nat) (q : Program arity) (tag : Nat),
    (nodes p)[tag]? = some ⟨arity,q⟩ →
  ∀ (ctx : Nat) (args : List.Vector (Term ctx) arity),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (atTerms q (call tag args) args))

/-- The SAME original arithmetic graph characterizes the actual named call.
No alternative function coding or source-theory extension is allowed. -/
def ExactNamedGraph : Prop :=
  ∀ (n : Nat) (p : Program n) (arity : Nat) (q : Program arity) (tag : Nat),
    (nodes p)[tag]? = some ⟨arity,q⟩ →
  ∀ (ctx : Nat) (out : Term ctx) (args : List.Vector (Term ctx) arity),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (GorbowBooleanTruth.biconditional (atTerms q out args) (.equal (call tag args) out)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraph.Targets

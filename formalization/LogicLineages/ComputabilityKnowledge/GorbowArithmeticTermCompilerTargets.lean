module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompilerDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector

def ActualEvaluation : Prop := ∀ n (t : Term n), arithmetic t →
  ∀ (v : List.Vector Nat n) (I : Interpretation),
  evaluate (compile t) v = t.realize I v.get

/-- Genuine internal correctness, even when the substituted arguments contain
the source universalFunction or other non-arithmetic subterms. -/
def InternalCompiler : Prop := ∀ n (t : Term n), arithmetic t →
  ∀ m (p : Program m) tag, (nodes p)[tag]? = some ⟨n, compile t⟩ →
  ∀ ctx (sigma : Fin n → Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call tag (List.Vector.ofFn sigma))
      (GorbowSubstitution.substitute sigma t)))

def HeaderCoverage : Prop := ∀ arity tag, arithmetic (headerTemplate arity tag)

/-- The actual arithmetic source header, not merely an externally equivalent
encoding. Its literal compiled AST is fixed by the definitions above. -/
def InternalHeaders : Prop := ∀ arity sourceTag m (p : Program m) registryTag,
  (nodes p)[registryTag]? = some ⟨arity, compile (headerTemplate arity sourceTag)⟩ →
  ∀ ctx (args : List.Vector (Term ctx) arity),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (GorbowPRDefiningEquations.call registryTag args)
      (GorbowRegistryTuple.headerTerm arity sourceTag args.toList)))

def Target : Prop := ActualEvaluation ∧ InternalCompiler ∧ HeaderCoverage ∧ InternalHeaders

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler.Targets

module

public import LogicLineages.ComputabilityKnowledge.GorbowOrdinaryArithmeticGraphsDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth

@[expose] public section
/-! Literal original arithmetic graph at arbitrary source-language terms.
No semantic evaluator, graph-correctness axiom or truth-to-proof premise is
part of this definition. Output remains index zero before substitution. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraph
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations

def atTerms {arity ctx : Nat} (q : Program arity) (out : Term ctx)
    (args : List.Vector (Term ctx) arity) : Formula ctx :=
  GorbowFormulaSubstitution.substituteFormula (Fin.cases out args.get)
    (GorbowOrdinaryArithmeticGraphs.graph q)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.NamedArithmeticGraph

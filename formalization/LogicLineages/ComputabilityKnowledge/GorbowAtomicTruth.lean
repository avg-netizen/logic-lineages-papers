module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicParameters
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionComposition

@[expose] public section
/-! Each literal L-minus atomic source schema, over its arbitrary precisely
occurring names and closed arithmetic term codes. This is a semantic schema
family, not a recursive axiom recognizer or represented Base/DCB theory. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth
open GorbowSyntax GorbowRegistryTuple GorbowSortedSyntaxCode GorbowAtomicParameters

def instanceCodeTerm {n m : Nat} (R : Formula m) (names : Fin n → Fin m) : Term n :=
  .universalFunction (headerTerm 3 1 [Term.numeral m,formulaQuote n R,argumentTuple names])

def atomicBody {n m : Nat} (R : Formula m) (names : Fin n → Fin m) : Formula n :=
  GorbowBooleanTruth.biconditional (.truth (instanceCodeTerm R names))
    (GorbowFormulaSubstitution.substituteFormula (valueDictionary names) R)

def atomicAxiom {n m : Nat} (R : Formula m) (names : Fin n → Fin m) : Sentence :=
  arithmeticClosure (atomicBody R names)
end LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth

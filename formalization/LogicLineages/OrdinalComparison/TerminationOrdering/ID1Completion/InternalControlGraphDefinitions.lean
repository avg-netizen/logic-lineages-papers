module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraph
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open LogicLineages.ComputabilityKnowledge

/-- The unchanged original arithmetic compiler applied to an existing concrete AST. -/
def programGraph {n : Nat} {α : Type} (p : GorbowPRProgram.Program n)
    (out : OTerm α) (xs : Fin n → OTerm α) : Formula α :=
  graph (OrdinaryArithmetic.graphFormula p) out xs

def equal {α : Type} (s t : OTerm α) : Formula α :=
  arithmeticEmbedding.onFormula (s.equal t)

/-- Exact equality-test output, including the rejecting case. -/
def testSpec {α : Type} (out input pivot : OTerm α) : Formula α :=
  (equal input pivot ⊓ equal out (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)) ⊔
  ((equal input pivot).not ⊓ equal out OrdinaryArithmetic.zeroTerm)

/-- The original conditional takes control first, then the zero branch, then
its nonzero branch. No implicit normalization or truthiness change is made. -/
def conditionalSpec {α : Type} (out control zeroBranch otherBranch : OTerm α) : Formula α :=
  (equal control OrdinaryArithmetic.zeroTerm ⊓ equal out zeroBranch) ⊔
  ((equal control OrdinaryArithmetic.zeroTerm).not ⊓ equal out otherBranch)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraph

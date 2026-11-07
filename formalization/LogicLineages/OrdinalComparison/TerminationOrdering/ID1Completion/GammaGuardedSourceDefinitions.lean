module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSource
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- An ORIGINAL unary Program applied to one original input coordinate. -/
def atInput {m : Nat} (p : Program 1) (i : Fin m) : Program m :=
  .composition p ![.projection i]

/-- Equality of the outputs of ONE shared decoder-based Gamma Program. -/
def sameGamma {m : Nat} (gamma : Program 1) (i j : Fin m) : Program m :=
  .composition InternalEqualityTest.equalityTest ![atInput gamma i,atInput gamma j]

def baseTyped (typed : Program 3) (valid : Program 1) : Program 3 :=
  InternalAcceptance.conjunction typed (atInput valid 2)

/-- Both objects must be valid. Equality of default outputs alone is insufficient. -/
def guard (valid gamma : Program 1) : Program 2 :=
  InternalAcceptance.conjunction (atInput valid 0)
    (InternalAcceptance.conjunction (atInput valid 1) (sameGamma gamma 0 1))

def basePositive (positive : Program 4) (gamma : Program 1) : Program 4 :=
  InternalAcceptance.conjunction positive (sameGamma gamma 1 2)

def baseSource (old : SourcePresentation.Data) (gamma : Program 1) : SourcePresentation.Data :=
  { old with positive := basePositive old.positive gamma }

/-- Application stays the literal original checker. -/
def baseComputability (old : JointGammaComputability.Data) (valid gamma : Program 1) :
    JointGammaComputability.Data :=
  { old with typed := baseTyped old.typed valid, guard := guard valid gamma }

def source (old : SourcePresentation.Data) (typed : Program 3)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1) : SourcePresentation.Data :=
  GuardedSource.source (baseSource old gamma) (baseTyped typed valid) tag window

def computability (old : JointGammaComputability.Data) (valid gamma : Program 1)
    (tag : Program 2) : JointGammaComputability.Data :=
  GuardedSource.computability (baseComputability old valid gamma) tag

/-- The exact ordinary-arithmetic embedding of the ORIGINAL checker formula. -/
def literalGuard {α : Type} (data : JointGammaComputability.Data)
    (x u : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula ((SourcePresentation.checkerFormula data.guard).subst ![x,u])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSource

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSource
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One shared ORIGINAL Program is used for every occurrence of T(c,o). -/
def typedTag (tag : Program 2) : Program 3 :=
  .composition tag ![.projection 0,.projection 2]

def typedMatch (tag : Program 2) : Program 3 :=
  .composition InternalEqualityTest.equalityTest ![.projection 1,typedTag tag]

/-- Exact-one original typed checker AND equality of its type with T(c,o). -/
def guardedTyped (typed : Program 3) (tag : Program 2) : Program 3 :=
  InternalAcceptance.conjunction typed (typedMatch tag)

def leftTag (tag : Program 2) : Program 4 :=
  .composition tag ![.projection 0,.projection 1]

def rightTag (tag : Program 2) : Program 4 :=
  .composition tag ![.projection 0,.projection 2]

def sourceTyped (typed : Program 3) (tag : Program 2) : Program 4 :=
  .composition typed ![.projection 0,leftTag tag,.projection 1]

def targetTyped (typed : Program 3) (tag : Program 2) : Program 4 :=
  .composition typed ![.projection 0,rightTag tag,.projection 2]

def sameTag (tag : Program 2) : Program 4 :=
  .composition InternalEqualityTest.equalityTest ![leftTag tag,rightTag tag]

def windowAt (window : Program 1) : Program 4 :=
  .composition window ![.projection 0]

/-- Activation requires BOTH window validity and a typed SOURCE. -/
def activation (typed : Program 3) (tag : Program 2) (window : Program 1) : Program 4 :=
  InternalAcceptance.conjunction (windowAt window) (sourceTyped typed tag)

def acceptedTarget (positive : Program 4) (typed : Program 3) (tag : Program 2) : Program 4 :=
  InternalAcceptance.conjunction positive
    (InternalAcceptance.conjunction (targetTyped typed tag) (sameTag tag))

/-- Inactive inputs return the LITERAL OLD OUTPUT. In particular a positive
edge with no typed source is never silently rejected. -/
def guardedPositive (positive : Program 4) (typed : Program 3)
    (tag : Program 2) (window : Program 1) : Program 4 :=
  InternalAcceptance.branch (activation typed tag window) positive
    (acceptedTarget positive typed tag)

def source (old : SourcePresentation.Data) (typed : Program 3)
    (tag : Program 2) (window : Program 1) : SourcePresentation.Data :=
  { old with positive := guardedPositive old.positive typed tag window }

def computability (old : JointGammaComputability.Data) (tag : Program 2) :
    JointGammaComputability.Data :=
  { old with typed := guardedTyped old.typed tag }

/-- The ORIGINAL typedFormula, instantiated at the original numeric context. -/
def literalTyped {α : Type} (data : JointGammaComputability.Data) (context : Nat)
    (typ object : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula ((JointGammaTyped.typedFormula data.typed).subst
    ![numeral context,typ,object])

/-- The ORIGINAL existential certificateGraph, not a selected certificate. -/
def literalR {α : Type} (data : SourcePresentation.Data) (context : Nat)
    (x y : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula ((OrdinaryArithmeticQuotient.certificateGraph data.positive).subst
    ![numeral context,x,y])

/-- Literal original C_tau formula at the original context and object term. -/
def literalComputable {α : Type} (data : JointGammaComputability.Data)
    (context : Nat) (tau : Ty) (x : OrdinaryArithmetic.Term α) : Formula α :=
  (JointGammaComputability.formula data tau).subst
    (fun i => arithmeticEmbedding.onTerm (![numeral context,x] i))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSource

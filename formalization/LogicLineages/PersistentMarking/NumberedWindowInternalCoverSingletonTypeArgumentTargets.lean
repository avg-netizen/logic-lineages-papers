module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalPairing (pairing)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalMultiplicationLawsProof (mul)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ArgsMeasureCalibrated selectedArgsMeasure)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)

/-- Positive canonical original sparse cons, with literal zero tail
and exactly tag-3/arity-one on its actual head. -/
def singletonTypeGuard : Program 1 :=
  conjunction cellGood (conjunction (applyUnary (header 3 1) cellHead)
    (applyUnary LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.zeroTest cellTail))

def singletonPair20 : Program 1 := .composition pairing ![literal 1 2,constantZero 1]

def singletonTypeArgs (A : Program 1) : Program 1 := branch singletonTypeGuard A singletonPair20

abbrev singletonTypeKey {α : Type} (ty : OTerm α) := rawCons (typeLeafTerm ty) z

abbrev singletonMeasureCode {α : Type} : OTerm α :=
  add (add (mul (numeral 2) (numeral 2)) (numeral 2)) z

def ExactCoverSingletonTypeArgs : Prop :=
  ∀ A : Program 1, ArgsMeasureCalibrated A → ArgsMeasureCalibrated (singletonTypeArgs A)

def ExactOpenCoverSingletonTypeArgument : Prop :=
  ∀ (A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty : OTerm α),
    Nonempty (Derivation body Γ (unary (selectedArgsMeasure (singletonTypeArgs A))
      singletonMeasureCode (singletonTypeKey ty)))

def ExactOpenCoverSingletonTypeOccurrence : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (H K ty one ts₁ as₁ two ts₂ as₂ : OTerm α),
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (observed (numeral 1) H K z one ts₁ as₁)) →
    Nonempty (Derivation body Γ (observed (numeral 2) H K z two ts₂ as₂)) →
    Nonempty (Derivation body Γ (memberGraph as₂ (singletonTypeKey ty)))

/-- Same selected V/W and actual scratch with the precise reselection of A.
The physical stored type is still required to occur on the real K axis. -/
def ExactOpenCoverOrdinarySingletonTypeScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h ty p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (singletonTypeArgs A) B T) s body Γ
      (ordinaryKey h (singletonTypeKey ty)) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h (singletonTypeKey ty))))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentTargets

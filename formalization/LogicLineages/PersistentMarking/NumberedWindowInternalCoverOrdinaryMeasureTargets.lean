module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (measurePair)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaBump)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverSelectedGrammarNullaryTargets (nullaryKey)
open NumberedWindowInternalCoverHeadDispatchTargets (headPrograms)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverHeadWindowTargets (headPrior)

def ArgsMeasureCalibrated (A : Program 1) : Prop :=
  ∀ a, evaluate A (a ::ᵥ nil) = Encodable.encode (bounds a).2

/-- Original empty argument measurement is the unshifted standard pair (0,0),
whose actual numeric code is zero. Other arguments use the chosen callback. -/
def selectedArgsMeasure (A : Program 1) : Program 1 :=
  branch (.projection 0) (constantZero 1) A

def ordinaryArgumentCode (A : Program 1) : Program 1 :=
  .composition (selectedArgsMeasure A) (fun _ : Fin 1 => field 1)

def ordinarySelectedBump (A : Program 1) : Program 1 :=
  .composition lambdaBump (fun _ : Fin 1 => ordinaryArgumentCode A)

def ordinaryMeasureBase (M A : Program 1) : Program 1 :=
  branch (header 4 2) M (ordinarySelectedBump A)

abbrev ordinarySharedMeasure (M A : Program 1) : Program 1 :=
  namedSharedMeasure (ordinaryMeasureBase M A)

abbrev ordinaryPrograms (s : Settings) (V TV M A : Program 1) (B : Program 2) (T : Program 1) : Programs :=
  headPrograms s V TV (ordinaryMeasureBase M A) B T

abbrev ordinaryPrior {α : Type} (h a : OTerm α) : OTerm α := headPrior false h [a]

def ExactCoverSelectedArgsMeasure : Prop :=
  ∀ A : Program 1, ArgsMeasureCalibrated A → ArgsMeasureCalibrated (selectedArgsMeasure A)

def ExactCoverOrdinaryMeasureBase : Prop :=
  ∀ M A : Program 1, TermMeasureCalibrated M → ArgsMeasureCalibrated A →
    TermMeasureCalibrated (ordinaryMeasureBase M A)

def ExactCoverOrdinarySharedMeasure : Prop :=
  ∀ M A : Program 1, TermMeasureCalibrated M → ArgsMeasureCalibrated A →
    TermMeasureCalibrated (ordinarySharedMeasure M A)

def ExactOpenCoverOrdinaryMeasureCut : Prop :=
  ∀ (M A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p : OTerm α),
    Nonempty (Derivation body Γ (unary (ordinarySharedMeasure M A) p (ordinaryKey h a))) →
    Nonempty (Derivation body Γ
      (unary (ordinarySelectedBump A) p (ordinaryKey h a)))

def ExactOpenCoverOrdinaryArgumentPair : Prop :=
  ∀ (M A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p : OTerm α) (Q : Formula α),
    Nonempty (Derivation body Γ (unary (ordinarySharedMeasure M A) p (ordinaryKey h a))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m d width : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary (selectedArgsMeasure A) m (a.relabel j))) →
      Nonempty (Derivation body Δ (codePair m d width)) →
      Nonempty (Derivation body Δ (measurePair (p.relabel j) d width)) →
      Nonempty (Derivation body Δ (ltF d (suc d))) →
      Nonempty (Derivation body Δ (ltF width (suc width))) →
      Nonempty (Derivation body Δ (Q.relabel j))) →
    Nonempty (Derivation body Γ Q)

def ExactOpenCoverOrdinaryNullaryPair : Prop :=
  ∀ (M A : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h p : OTerm α),
    Nonempty (Derivation body Γ (unary (ordinarySharedMeasure M A) p (nullaryKey h))) →
    Nonempty (Derivation body Γ (measurePair p z z))

def ExactOpenCoverOrdinaryNullaryFitted : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h p vertices ctx result : OTerm α),
    ParentRow (ordinaryPrograms s V TV M A B T) s body Γ (nullaryKey h) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (nullaryKey h)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureTargets

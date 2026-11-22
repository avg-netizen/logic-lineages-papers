module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase lexicalNamedWindow)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)

/-- Actual optional result on [ctx,raw], returned only if the same original
intrinsic fallback gives a nonzero result on that same tape. -/
def storedTypeResult : Program 2 := .composition .succ (fun _ : Fin 1 => onRaw (field 0))

def namedPositiveResult (B : Program 2) : Program 2 := branch B (constantZero 2) storedTypeResult

def namedResultAt (b : Bool) (B : Program 2) : Program 2 :=
  branch (onRaw (header b.toNat 2)) B (namedPositiveResult B)

def namedResultBase (B : Program 2) : Program 2 := namedResultAt false (namedResultAt true B)

abbrev namedResultWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  lexicalNamedWindow s (namedResultBase B) T

def ExactCoverNamedResultAt : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2), IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (namedResultAt b B)

def ExactCoverNamedResultWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    ActualPackedWindow s (namedResultWindow s B T)

def ExactOpenCoverNamedResultBase : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ (programGraph
      (leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B))))
      (suc result) ![ctx,namedTerm b.toNat ty i])) →
    Nonempty (Derivation body Γ (eqn result ty))

def ExactOpenCoverNamedResultWindow : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (namedResultWindow s B T) ctx result (namedTerm b.toNat ty i))) →
    Nonempty (Derivation body Γ (eqn result ty))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets

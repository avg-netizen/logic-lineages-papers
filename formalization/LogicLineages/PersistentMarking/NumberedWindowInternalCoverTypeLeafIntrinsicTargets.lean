module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAcceptance (branch constantZero)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)

def onRaw (P : Program 1) : Program 2 := .composition P (fun _ : Fin 1 => .projection 1)

def leafTypeTest (s : Settings) : Program 1 :=
  .composition (grammarTypeAt s) (fun _ : Fin 1 => field 0)

/-- For the literal canonical type-only constructor, require real finite
grammar membership in addition to the old same-context computation B.
Every other input still runs the unchanged B at the same two inputs.
The check is independent of numeral width and never fabricates an accepted type. -/
def leafIntrinsicBase (s : Settings) (B : Program 2) : Program 2 :=
  branch (onRaw (header 3 1)) B
    (branch (normalize (onRaw (leafTypeTest s))) (constantZero 2) B)

abbrev leafStrictWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  strictAuxWindow (leafIntrinsicBase s B) T

def ExactCoverTypeLeafIntrinsicBase : Prop :=
  ∀ (s : Settings) (B : Program 2), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → IntrinsicWindowCalibrated s (leafIntrinsicBase s B)

def ExactCoverTypeLeafIntrinsicWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T → ActualPackedWindow s (leafStrictWindow s B T)

def ExactOpenCoverTypeLeafShape : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty : OTerm α),
    Nonempty (Derivation body Γ (unary termShape z (typeLeafTerm ty))) ∧
    Nonempty (Derivation body Γ (unary (header 3 1) (suc z) (typeLeafTerm ty))) ∧
    Nonempty (Derivation body Γ (unary (field 0) ty (typeLeafTerm ty)))

def ExactOpenCoverTypeLeafIntrinsicBaseK : Prop :=
  ∀ (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty result : OTerm α),
    Nonempty (Derivation body Γ (programGraph (leafIntrinsicBase s B) (suc result) ![ctx,typeLeafTerm ty])) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

/-- Actual accepted selected type-only window gives the original stored
field's finite grammar membership. No old-W or syntax reflection premise. -/
def ExactOpenCoverTypeLeafStrictWindowK : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (leafStrictWindow s B T) ctx result (typeLeafTerm ty))) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets

module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest leafStrictWindow)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)

def grammarGuard (s : Settings) (B : Program 2) : Program 2 :=
  branch (normalize (onRaw (leafTypeTest s))) (constantZero 2) B

def namedGrammarAt (b : Bool) (s : Settings) (B : Program 2) : Program 2 :=
  branch (onRaw (header b.toNat 2)) B (grammarGuard s B)

/-- Preserve exactly the previous type-only window by specializing its
original base parameter; do not assert equality of differently selected graphs. -/
def namedGrammarBase (s : Settings) (B : Program 2) : Program 2 :=
  namedGrammarAt false s (namedGrammarAt true s B)

abbrev namedGrammarWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  leafStrictWindow s (namedGrammarBase s B) T

def ExactCoverNamedLeafGrammarAt : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2),
    GrammarTypeInclusion s → IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (namedGrammarAt b s B)

def ExactCoverNamedLeafGrammarWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1),
    GrammarTypeInclusion s → IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    ActualPackedWindow s (namedGrammarWindow s B T)

def NamedKeyReports (b : Bool) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ty i : OTerm α) : Prop :=
  let raw := namedTerm b.toNat ty i
  Nonempty (Derivation body Γ (unary termShape z raw)) ∧
  Nonempty (Derivation body Γ (unary (header 3 1) z raw)) ∧
  Nonempty (Derivation body Γ (unary (header b.toNat 2) (suc z) raw)) ∧
  Nonempty (Derivation body Γ (unary (field 0) ty raw)) ∧
  Nonempty (Derivation body Γ (unary (field 1) i raw)) ∧
  (b = true → Nonempty (Derivation body Γ (unary (header 0 2) z raw)))

def ExactOpenCoverNamedLeafIntrinsicShape : Prop :=
  ∀ (b : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty i : OTerm α),
    NamedKeyReports b body Γ ty i

def ExactOpenCoverNamedLeafIntrinsicBaseK : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ
      (programGraph (NumberedWindowInternalCoverTypeLeafIntrinsicTargets.leafIntrinsicBase s (namedGrammarBase s B))
        (suc result) ![ctx,namedTerm b.toNat ty i])) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

def ExactOpenCoverNamedLeafGrammarWindowK : Prop :=
  ∀ (b : Bool) (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (namedGrammarWindow s B T) ctx result (namedTerm b.toNat ty i))) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets

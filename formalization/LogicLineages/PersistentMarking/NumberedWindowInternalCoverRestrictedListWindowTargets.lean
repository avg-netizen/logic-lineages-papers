module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedNumberedListTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowInternalSparsePathEnvelope (applyUnary field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets (typeOnlyHeadGuard)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated intrinsicWindow)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def listSlotAllowed (G : Program 1) (i : Nat) : Program 1 :=
  applyUnary GorbowPRInternalControl.zeroTest (applyUnary (argumentReject G) (field i))

def ordinaryListAllowed (G : Program 1) : Program 1 := listSlotAllowed G 1
def numberedListAllowed (G : Program 1) : Program 1 :=
  conjunction (listSlotAllowed G 3) (listSlotAllowed G 4)

def keepWhenListAllowed (P : Program 1) (B : Program 2) : Program 2 :=
  branch (normalize (onRaw P)) (constantZero 2) B

/-- A deliberately restricted variant. Other canonical tags and malformed
headers take unchanged B at this local callback; ordinary and numbered may
be rejected even when they were valid before. -/
def restrictedListBase (G : Program 1) (B : Program 2) : Program 2 :=
  branch (onRaw (header 4 2))
    (branch (onRaw (header 5 5)) B (keepWhenListAllowed (numberedListAllowed G) B))
    (keepWhenListAllowed (ordinaryListAllowed G) B)

abbrev restrictedListWindow (s : Settings) (G : Program 1) (B : Program 2) (T : Program 1) :=
  lambdaLexicalWindow s (restrictedListBase G B) T

def OriginalTypeOnlyArguments (s : Settings) (a : Nat) : Prop :=
  ∃ xs, unpack a = some xs ∧ ∀ q ∈ xs, ∃ ty, unpackNode q = some (3,[ty]) ∧ ty ∈ s.types

def OriginalTypeOnlyParentDomain (s : Settings) (raw : Nat) : Prop :=
  (∀ h a, unpackNode raw = some (4,[h,a]) → OriginalTypeOnlyArguments s a) ∧
  (∀ h ty k l r, unpackNode raw = some (5,[h,ty,k,l,r]) →
    OriginalTypeOnlyArguments s l ∧ OriginalTypeOnlyArguments s r)

/-- Exact conditional fit of the deepest two-input callback only; not a
claim of global calibration of the full contextual W or its child graphs. -/
def ExactCoverRestrictedListBaseNumeric : Prop :=
  ∀ (s : Settings) (B : Program 2), IntrinsicWindowCalibrated s B →
    ∀ ctx raw,
      (OriginalTypeOnlyParentDomain s raw →
        evaluate (restrictedListBase (typeOnlyHeadGuard s) B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw) ∧
      (¬OriginalTypeOnlyParentDomain s raw →
        evaluate (restrictedListBase (typeOnlyHeadGuard s) B) (ctx ::ᵥ raw ::ᵥ nil) = 0)

def ExactOpenCoverRestrictedOrdinaryListReport : Prop :=
  ∀ (s : Settings) (G : Program 1) (B : Program 2) (T : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx h a result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (restrictedListWindow s G B T) ctx result (ordinaryKey h a))) →
    Nonempty (Derivation body Γ (unary (argumentReject G) z a))

def ExactOpenCoverRestrictedNumberedListReports : Prop :=
  ∀ (s : Settings) (G : Program 1) (B : Program 2) (T : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx h ty k l r result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (restrictedListWindow s G B T) ctx result (numberedTerm h ty k l r))) →
    Nonempty (Derivation body Γ (unary (argumentReject G) z l)) ∧
    Nonempty (Derivation body Γ (unary (argumentReject G) z r))

abbrev restrictedTypeOnlyPrograms (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) :=
  lexicalFittedPrograms s V TV M (argumentMeasure (typeLeafSharedMeasure M0))
    (restrictedListBase (typeOnlyHeadGuard s) B) T

def ExactOpenCoverRestrictedOrdinaryTypeOnlyScratch : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h a p vertices ctx result : OTerm α),
    ParentRow (restrictedTypeOnlyPrograms s V TV M M0 B T) s body Γ (ordinaryKey h a)
      p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

def ExactOpenCoverRestrictedNumberedTypeOnlyScratch : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h ty k l r p vertices ctx result : OTerm α),
    ParentRow (restrictedTypeOnlyPrograms s V TV M M0 B T) s body Γ (numberedTerm h ty k l r)
      p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets

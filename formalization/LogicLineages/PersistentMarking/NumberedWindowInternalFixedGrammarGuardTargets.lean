module

public import LogicLineages.PersistentMarking.NumberedWindowFixedGrammarTypeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Physical standard scratch membership in the actual full grammar type
list, at the original open input; no window-list value is substituted. -/
def grammarTypeAt (S : Spine.Signature) (K : List Ty) : Program 1 :=
  .composition scratchMember ![literal 1 (Encodable.encode (fixed S K).types),.projection 0]

/-- Deliberate reselection of the type-guard AST. Its left conjunct is
the same supplied T. Its right conjunct is a literal grammar membership
report, not a new predicate known only by numerical equivalence. -/
def refitGuard (S : Spine.Signature) (K : List Ty) (T : Program 1) : Program 1 :=
  conjunction T (grammarTypeAt S K)

def ExactRefitGuardCalibration : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (T : Program 1),
    TypeGuardCalibrated (fixed S K) T → TypeGuardCalibrated (fixed S K) (refitGuard S K T)

/-- The rule is only for the literal reselected guard on its actual tape.
It gives both the unchanged original guard graph and the physical grammar
type occurrence. No corresponding rule for an arbitrary old T is assumed. -/
def ExactOpenRefitGuardReports : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (T : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ty : OTerm α),
    let source := unary (refitGuard S K T) (suc z) ty
    let reports := unary T (suc z) ty ⊓
      memberGraph (numeral (Encodable.encode (fixed S K).types)) ty
    Nonempty (Derivation body Γ ((source.imp reports) ⊓ (reports.imp source)))

end LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardTargets

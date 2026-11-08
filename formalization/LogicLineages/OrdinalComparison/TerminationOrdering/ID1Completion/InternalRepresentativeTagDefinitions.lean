module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTag
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A concrete unary AST. On exact-one validity it retains the RAW input's
outer type field and the OLD representative's payload; otherwise it returns
zero. The normalization tests equality to one, not generic nonzero truth. -/
def representative (valid oldRepresentative : Program 1) : Program 1 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize valid)
    (InternalAcceptance.constantZero 1)
    (pairOf InternalUnpair.left (rightOf oldRepresentative))

/-- Both wrappers reuse the exact validity leaves of the original step guard.
The source retains its universe filter; the target retains only packed decode.
The supplied step AST is preserved literally. This record has no proof fields. -/
def withRepresentatives (validity : InternalOriginalStepGuard.Data)
    (old : InternalQuotientEdgeChecker.Data) : InternalQuotientEdgeChecker.Data where
  stepProgram := old.stepProgram
  sourceRepresentative := representative validity.sourceValid old.sourceRepresentative
  targetRepresentative := representative validity.targetValid old.targetRepresentative

/-- Validity and representative output are actual original arithmetic graphs.
In particular, validity is not inferred internally from external calibration. -/
def representation {α : Type} (valid oldRepresentative : Program 1)
    (out raw : OTerm α) : Formula α :=
  graph1 valid InternalOriginalStepGuard.one raw ⊓
    graph1 (representative valid oldRepresentative) out raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTag

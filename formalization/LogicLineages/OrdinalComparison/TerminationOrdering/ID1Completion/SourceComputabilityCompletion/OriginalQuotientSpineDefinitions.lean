module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpine
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal original quotient edge implies the existing conditional
bottom-spine guard at its SAME canonical endpoints, certificate and runtime
parameter. Raw certificate fields, whole marks, depths and source types are
bound internally; the caller supplies only the original active window and
accepted quotient edge. This transfers the raw guard through the SAME full
canonical folds. It neither identifies an edge with a source H+ certificate
nor supplies finite-type computability or the paper06 all-term theorem. -/
def QuotientHasSpineGuard (data : Data) (window : Program 1) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window source parameter ⊓
        UniformCertificateCompletion.edgeAccepted data oldStep source target certificate parameter).imp
      (OriginalSpineGuardLeaf.spineAccepted source target certificate parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpine

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniformStepQuotientTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both actual canonical outputs and the original encoded quotient certificate
are retained with the SAME accepted raw step, both original source-validity
graphs and the literal UniformCertificateCompletion quotient checker. -/
def Recovered {alpha : Type} (data : Data) (oldStep : Program 4)
    (source target step sourceOut targetOut certificate parameter : OTerm alpha) : Formula alpha :=
  stepAccepted data oldStep source target step parameter ⊓
    (graph2 (validity data) InternalOriginalStepGuard.one source parameter ⊓
      (graph2 (validity data) InternalOriginalStepGuard.one target parameter ⊓
        (InternalParameterizedCanonicalResultFold.foldGraph data sourceOut source parameter ⊓
          (InternalParameterizedCanonicalResultFold.foldGraph data targetOut target parameter ⊓
            (graph3 edgeCode certificate source target step ⊓
              edgeAccepted data oldStep sourceOut targetOut certificate parameter)))))

/-- An accepted original raw step supplies a quotient edge of the SAME checker.
Both actual canonical-fold outputs and the original edgeCode certificate are
bound internally by Program totality. No output, fold, filtered-source graph,
target graph, calibration or normalized-checker premise is supplied. The raw
endpoints, step certificate and symbolic parameter are transported literally. -/
def ActualOriginalUniformStepQuotientElimination : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (alpha : Type) (Gamma : List (Formula alpha))
    (source target step parameter : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma (stepAccepted data oldStep source target step parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ sourceOut targetOut certificate : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered data oldStep (source.relabel j) (target.relabel j) (step.relabel j)
        sourceOut targetOut certificate (parameter.relabel j))) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniformStepQuotientTargets

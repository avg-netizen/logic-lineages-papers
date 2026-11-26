module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentLambdaFinalFold OriginalTransparentLambdaFinalFoldLaws
open OriginalTransparentLambdaFinalFoldSyntaxProof OriginalTransparentLambdaFinalFoldBindingProof
open OriginalTransparentLambdaFinalFoldInductionProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
variable (guard leaf valid : Program 2) (combine : Program 5)
variable (hleaf : LeafLaw body guard leaf valid)
variable (happ : ApplicationLaw body guard valid combine)
include hleaf happ

/-- The common output from genuine internal payload induction identifies
any supplied fold output with the comparison output, including rejection. -/
theorem foldToValid (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
        out input parameter))) :
    Nonempty (Derivation body Gamma (graph2 valid out input parameter)) := by
  apply hasCertifiedOutputCases guard leaf valid combine input parameter _
    (commonOutputExists guard leaf valid combine hleaf happ input parameter)
  intro β j Delta produced hj hc
  rw [graph2Rename]
  have h' := renameInto h j Delta hj
  rw [graph2Rename] at h'
  have he := valueUnique (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
    produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (andRight (andLeft hc)) h'
  exact outputTransport valid produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he (andRight hc)

/-- Functionality of the comparison program provides the reverse direction
without requiring acceptance, output positivity, or an extra recurrence premise. -/
theorem validToFold (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 valid out input parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
        out input parameter)) := by
  apply hasCertifiedOutputCases guard leaf valid combine input parameter _
    (commonOutputExists guard leaf valid combine hleaf happ input parameter)
  intro β j Delta produced hj hc
  rw [graph2Rename]
  have h' := renameInto h j Delta hj
  rw [graph2Rename] at h'
  have he := valueUnique valid produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (andRight hc) h'
  exact outputTransport (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
    produced (out.relabel j)
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    he (andRight (andLeft hc))

/-- Generic internal all-output absorption for the unchanged original
application fold. The two auxiliary callback laws must be proved when used. -/
theorem allOutputEquation (out input parameter : OTerm α) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
          out input parameter).iff (graph2 valid out input parameter))) := by
  let fold := graph2 (InternalParameterizedApplicationResultStack.foldP guard leaf combine)
    out input parameter
  let comparison := graph2 valid out input parameter
  obtain ⟨hf⟩ := foldToValid (Gamma := fold :: Gamma)
    guard leaf valid combine hleaf happ out input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := validToFold (Gamma := comparison :: Gamma)
    guard leaf valid combine hleaf happ out input parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldProof

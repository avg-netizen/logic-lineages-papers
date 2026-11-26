module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalContextInsertion
open OriginalContextInsertionSyntaxProof (insertRename)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportSyntaxProof
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem sourceContextRename {beta : Type} (erasing : Bool)
    (gamma extended : OTerm alpha) (j : alpha → beta) :
    (sourceContext erasing gamma extended).relabel j =
      sourceContext erasing (gamma.relabel j) (extended.relabel j) := by
  cases erasing <;> rfl

@[simp] theorem targetContextRename {beta : Type} (erasing : Bool)
    (gamma extended : OTerm alpha) (j : alpha → beta) :
    (targetContext erasing gamma extended).relabel j =
      targetContext erasing (gamma.relabel j) (extended.relabel j) := by
  cases erasing <;> rfl

/-- Both original encoded contexts extend by the SAME literal domain. -/
theorem sourceCons (erasing : Bool) (domain gamma extended childGamma childExtended : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (StepCons childGamma domain gamma)))
    (he : Nonempty (Derivation body Delta (StepCons childExtended domain extended))) :
    Nonempty (Derivation body Delta (StepCons
      (sourceContext erasing childGamma childExtended) domain
      (sourceContext erasing gamma extended))) := by
  cases erasing
  · exact hg
  · exact he

theorem targetCons (erasing : Bool) (domain gamma extended childGamma childExtended : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (StepCons childGamma domain gamma)))
    (he : Nonempty (Derivation body Delta (StepCons childExtended domain extended))) :
    Nonempty (Derivation body Delta (StepCons
      (targetContext erasing childGamma childExtended) domain
      (targetContext erasing gamma extended))) := by
  cases erasing
  · exact he
  · exact hg

theorem childInsert (d cutoff gamma extended domain childGamma childExtended : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Insert d cutoff gamma extended)))
    (hg : Nonempty (Derivation body Delta (StepCons childGamma domain gamma)))
    (he : Nonempty (Derivation body Delta (StepCons childExtended domain extended))) :
    Nonempty (Derivation body Delta (Insert d (suc cutoff) childGamma childExtended)) :=
  OriginalContextInsertionConsProof.consBackward d cutoff childGamma childExtended domain gamma extended hg he hi

/-- Requested arrow/list fields are produced by the original total selectors.
Their nonzero/domain guards are left to the actual acceptance equation. -/
theorem arrowCases (typ : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (domain codomain : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepArrowFields (typ.relabel j) domain codomain)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 1 :=
    ![OriginalTypedDecoder.headOf (.projection 0),OriginalTypedDecoder.tailOf (.projection 0)]
  apply queryCases qs (Fin.cons typ Fin.elim0) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 1 → OTerm beta := ![typ.relabel j]
  exact next beta j Theta (ys 0) (ys 1) hj
    (arrowFields (.projection 0) (typ.relabel j) (ys 0) (ys 1) xs
      (projectionValue 0 xs) (hq 0) (hq 1))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof

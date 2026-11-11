module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinarySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeel
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityClosure
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalBinarySyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Expose the actual raw application tree behind the original packed
constructor. Both payload witnesses are generated internally. -/
theorem applicationCoordinatesCases (arrow d e fp ap fn arg parent : OTerm alpha)
    (psi : Formula alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg parent)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (raw middle : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StepPair (parent.relabel j) (e.relabel j) raw)) →
      Nonempty (Derivation body Delta (StepPair raw (numeral 2) middle)) →
      Nonempty (Derivation body Delta (StepBinaryPayload middle (d.relabel j) (fp.relabel j) (ap.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let children : Program 4 := pairOf (.projection 2) (.projection 3)
  let middle : Program 4 := pairOf (.projection 0) children
  let node : Program 4 := pairOf (two 4) middle
  let qs : Fin 3 → Program 4 := ![children,middle,node]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs psi
  intro beta j ys Delta hj hq
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hp := andRight (andRight (andRight hc'))
  have hchildren := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hmiddle := binaryRecover InternalPairing.pairing (.projection 0) children
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hnode := binaryRecover InternalPairing.pairing (two 4) middle
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have hparent := binaryRecover InternalPairing.pairing (.projection 1) node
    (parent.relabel j) (e.relabel j) (ys 2) xx hp (projectionValue 1 xx) (hq 2)
  exact step beta j Delta (ys 2) (ys 1) hj hparent hnode
    (stepBinaryPayloadIntro (ys 1) (d.relabel j) (fp.relabel j) (ap.relabel j) (ys 0)
      hmiddle hchildren)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof

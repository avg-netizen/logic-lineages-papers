module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportExposureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalPackedProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases selectorPair)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Expose the SAME input type, input raw payload and actual shifted payload
inside arithmetic. No packed-pair or successful raw-run premise is supplied. -/
theorem shiftPackedCases (packed shifted cutoff : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted cutoff packed)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (typ raw transformed : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (packed.relabel j) typ raw)) →
      Nonempty (Derivation body Theta (graph2 shiftRaw transformed (cutoff.relabel j) raw)) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (shifted.relabel j) typ transformed)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 3 → Program 2 := ![leftOf (.projection 1),rightOf (.projection 1),
    .composition shiftRaw ![.projection 0,rightOf (.projection 1)] ]
  apply programsCases ps (Fin.cons cutoff (Fin.cons packed Fin.elim0)) psi
  intro beta j Theta ys hj hy
  simp only [consTermRename,emptyRename] at hy
  let xs : Fin 2 → OTerm beta := ![cutoff.relabel j,packed.relabel j]
  have hp := selectorPair (.projection 1) (packed.relabel j) (ys 0) (ys 1) xs
    (projectionValue 1 xs) (hy 0) (hy 1)
  have ht := binaryRecover shiftRaw (.projection 0) (rightOf (.projection 1))
    (ys 2) (cutoff.relabel j) (ys 1) xs (hy 2) (projectionValue 0 xs) (hy 1)
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename] at hs'
  exact step beta j Theta (ys 0) (ys 1) (ys 2) hj hp ht
    (shiftPackedForward (packed.relabel j) (shifted.relabel j) (ys 0) (ys 1) (ys 2)
      (cutoff.relabel j) hp ht hs')

/-- The original ternary erasure wrapper provides its actual raw transform;
the unchanged outer type is recovered from the SAME original packed input. -/
theorem erasePackedCases (packed erased d cutoff : OTerm alpha) (psi : Formula alpha)
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d cutoff packed)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (typ raw transformed : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (packed.relabel j) typ raw)) →
      Nonempty (Derivation body Theta
        (graph3 eraseRaw transformed (d.relabel j) (cutoff.relabel j) raw)) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (erased.relabel j) typ transformed)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 3 → Program 3 := ![leftOf (.projection 2),rightOf (.projection 2),
    .composition eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)] ]
  apply programsCases ps (Fin.cons d (Fin.cons cutoff (Fin.cons packed Fin.elim0))) psi
  intro beta j Theta ys hj hy
  simp only [consTermRename,emptyRename] at hy
  let xs : Fin 3 → OTerm beta := ![d.relabel j,cutoff.relabel j,packed.relabel j]
  have hp := selectorPair (.projection 2) (packed.relabel j) (ys 0) (ys 1) xs
    (projectionValue 2 xs) (hy 0) (hy 1)
  have ht : Nonempty (Derivation body Theta
      (graph3 eraseRaw (ys 2) (d.relabel j) (cutoff.relabel j) (ys 1))) := by
    apply compositionRecover eraseRaw ![.projection 0,.projection 1,rightOf (.projection 2)]
      (ys 2) xs ![d.relabel j,cutoff.relabel j,ys 1] (hy 2)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (hy 1) (fun k => Fin.elim0 k))) i
  have he' := renameInto he j Theta hj
  simp only [graph3Rename] at he'
  exact step beta j Theta (ys 0) (ys 1) (ys 2) hj hp ht
    (erasePackedForward (packed.relabel j) (erased.relabel j) (ys 0) (ys 1) (ys 2)
      (d.relabel j) (cutoff.relabel j) hp ht he')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportExposureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderFinalTransportExposureProof

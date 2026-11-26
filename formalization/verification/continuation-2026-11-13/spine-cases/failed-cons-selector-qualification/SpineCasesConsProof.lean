module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atCons (H : Program 1) (M W : Program 2)
 (types raw gamma c domain head tail : OTerm alpha) (psi : Formula alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain head tail)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (requested tailTypes : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (StepArrowFields (types.relabel j) requested tailTypes)) →
   Nonempty (Derivation body Theta (TermAccepted H M W (domain.relabel j) (head.relabel j) (gamma.relabel j) (c.relabel j))) →
   Nonempty (Derivation body Theta (ArgumentsAccepted H M W tailTypes (tail.relabel j) (gamma.relabel j) (c.relabel j))) →
   Nonempty (Derivation body Theta (InternalLessThan.strictLess (tail.relabel j) (raw.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let qs : Fin 2 → Program 1 := ![headOf (.projection 0),tailOf (.projection 0)]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (![types]) psi
 intro beta j ys Theta hj hq
 have ht := OriginalTypedDecoderInternalScalarProof.arrowFields (.projection 0) (types.relabel j) (ys 0) (ys 1)
   (![types.relabel j]) (projectionValue 0 (![types.relabel j])) (hq 0) (hq 1)
 have ha' := renameInto ha j Theta hj
 have hc' := renameInto hc j Theta hj
 simp only [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.argumentsAcceptedRename,graph3Rename] at ha' hc'
 have hf := OriginalTypedDecoderTransportLogicalProof.iffForward
   (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W (raw.relabel j) (domain.relabel j)
     (head.relabel j) (tail.relabel j) (types.relabel j) (ys 0) (ys 1) (gamma.relabel j) (c.relabel j) hc' ht) ha'
 have hchildren := andRight (andRight hf)
 exact next beta j Theta (ys 0) (ys 1) hj ht (andLeft hchildren) (andRight hchildren)
   (OriginalTypedArgumentObservationsInternalBoundProof.rawTailBound (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) hc')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.SpineCasesConsProof

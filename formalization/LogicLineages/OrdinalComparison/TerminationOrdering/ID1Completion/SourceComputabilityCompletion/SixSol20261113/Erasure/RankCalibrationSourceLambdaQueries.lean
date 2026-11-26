module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceLambdaQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTypedDecoderInternalListProof (listTail)
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalLambdaConstructorGraphSyntaxProof (oneRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Retain the literal connected coordinate system from the original source
lambda opener, including the actual cons arrow recovered from source shape. -/
theorem actualCases (H G : Program 1) (M W : Program 2)
 (packed parameter : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) packed)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (arrow raw payload domain childRaw codomain c gamma extended child childParam : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (packed.relabel j) arrow raw)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing raw (numeral 1) payload)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing payload domain childRaw)) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode arrow domain codomain)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing child codomain childRaw)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parameter.relabel j) c gamma)) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode extended domain gamma)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParam c extended)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 apply OriginalTransparentDecoderValidatorCollapseLambdaCasesProof.lambdaCoordinatesCases packed parameter psi htag
 intro beta j Theta typ raw payload domain childRaw requestedDomain codomain c gamma extended child childParam hj hp ht hm hf hparam he hchild hcp
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,oneRename] at hs'
 have factors := iffForward
   (OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof.sourceLambdaCoordinatesIff H G M W
     (packed.relabel j) (parameter.relabel j) typ raw payload domain childRaw requestedDomain codomain
     child c gamma extended childParam hp ht hm hf hchild hparam he hcp) hs'
 have shape := lambdaShapeBackward (packed.relabel j) typ raw payload domain childRaw requestedDomain codomain
   hp ht hm hf (andRight (andRight (andLeft factors)))
 have hleft := InternalApplicationCertificateConstructorsSupportProof.pairLeft (packed.relabel j) typ raw hp
 have hdomain := rawDomainValue (packed.relabel j) typ raw payload domain childRaw hp ht hm
 have harrow := shapeArrowRecover (packed.relabel j) typ domain codomain hleft hdomain
   (listTail typ requestedDomain codomain hf) shape
 exact next beta j Theta typ raw payload domain childRaw codomain c gamma extended child childParam hj
   hp ht hm harrow hchild hparam he hcp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceLambdaQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSourceLambdaQueries

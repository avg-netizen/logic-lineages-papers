module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion

open InternalTagArithmeticSyntaxProof (suc)
open OriginalTypedDecoderTransportLogicalProof (iffBackward)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The lambda child observes exactly the same erased type and the cons of
the actual deleted context. These are graph recurrences, not context-key
covariance. Both original and deleted child contexts are actual cons graphs. -/
theorem shiftedLookupAndDeletion (gamma deleted childGamma childDeleted domain cutoff erasedType : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma domain gamma)))
 (hcd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted domain deleted)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType (suc cutoff) childGamma)) ∧
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt childDeleted (suc cutoff) childGamma)) := by
 exact ⟨iffBackward (OriginalAllPositionContextDeleteDropProof.lookupConsIff childGamma domain gamma cutoff erasedType hc) hl,
   iffBackward (OriginalAllPositionContextDeleteConsProof.deleteConsIff childGamma domain gamma cutoff childDeleted deleted hc hcd) hd⟩

open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)

/-- Recover the original child parameter's literal pair coordinates from
its actual selector graph and a queried cons context. -/
theorem childPair (value d e child parameter childParameter context gamma extended : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields value d e child parameter childParameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter context extended)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons value (Fin.cons parameter Fin.elim0)
 let domain : Program 2 := .composition OriginalLambdaTraversal.rawDomain (fun _ : Fin 1 => .projection 0)
 let ext : Program 2 := InternalApplicationCertificateConstructors.consOf domain (InternalApplicationCertificateConstructors.rightOf (.projection 1))
 have hc := unaryValue InternalUnpair.left (.projection 1) context parameter xs
   (pairLeft parameter context gamma hp) (projectionValue 1 xs)
 have hg := unaryValue InternalUnpair.right (.projection 1) gamma parameter xs
   (pairRight parameter context gamma hp) (projectionValue 1 xs)
 have hd := unaryValue OriginalLambdaTraversal.rawDomain (.projection 0) d value xs
   (andLeft (andRight hf)) (projectionValue 0 xs)
 have hext := binaryValue InternalListCodec.consCode domain (InternalApplicationCertificateConstructors.rightOf (.projection 1))
   extended d gamma xs he hd hg
 exact binaryRecover InternalPairing.pairing (InternalApplicationCertificateConstructors.leftOf (.projection 1)) ext
   childParameter context extended xs (andRight (andRight (andRight (andRight hf)))) hc hext

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof

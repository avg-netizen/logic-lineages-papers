module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalLambdaTraversalInternal
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions (C)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem inputConstructor (input d e child arrow : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input d e child arrow))) :
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)) := by
 apply OriginalPackedSourceLambdaChildProof.rawCoordinates input child d e arrow _ hf
 intro beta j Theta node inner payload hj ho hn hi hb
 rw [graph3Rename]
 have hf' := renameInto hf j Theta hj
 rw [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hf'
 exact OriginalLambdaConstructorGraphSyntaxProof.constructorBackward (input.relabel j) (d.relabel j)
   (e.relabel j) (child.relabel j) payload
   (pairRight (child.relabel j) (e.relabel j) payload hb)
   (OriginalLambdaConstructorGraphSupportProof.packedAtPairs (input.relabel j) (d.relabel j)
     (e.relabel j) payload (arrow.relabel j) inner node (andLeft (andRight (andRight hf'))) hi hn ho)

theorem fieldsAtParameter (input d e child arrow parameter childParameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input d e child arrow)))
 (hp : Nonempty (Derivation body Delta (graph2 OriginalLambdaTraversal.childParameter childParameter input parameter))) :
 Nonempty (Derivation body Delta (LambdaFields input d e child parameter childParameter)) := by
 have ha := InternalListCodecSupportProof.consDestruction arrow d e (andLeft (andRight (andRight hf)))
 have he := unaryValue InternalListCodec.tailCode OriginalLambdaTraversal.rawType e arrow (Fin.cons input Fin.elim0)
   (andLeft (andRight ha)) (andLeft (andRight hf))
 exact andIntro (andLeft hf) (andIntro (andLeft (andRight (andRight (andRight hf))))
   (andIntro he (andIntro (EvaluatorChildrenSourceLambdaCore.bodySelector input d e child arrow hf) hp)))

theorem outputType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input out parameter typ : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) out input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ out)) := by
 let r := refined p H G W P
 have hf := EvaluatorKeyDomainClosureSupportProof.factors p H G W input parameter hd
 have hs := EvaluatorKeyCanonicalDomainSupportProof.sourceToLeaf p H G W P input parameter (andRight hf)
 have hi := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window out input typ parameter
   (andIntro (andLeft hf) (andIntro (andIntro hs ht) hc))
 exact andLeft (andRight hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaSupportProof

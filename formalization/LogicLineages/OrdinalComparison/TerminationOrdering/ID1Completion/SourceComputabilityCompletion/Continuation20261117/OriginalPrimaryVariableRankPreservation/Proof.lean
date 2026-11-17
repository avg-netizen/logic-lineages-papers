module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.GenericPrimaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.ConcreteClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem primaryVariableRankPreservation : Targets.InternalPrimaryVariableRankPreservation := by
 intro n arity body alpha Delta seed parameter out candidate seedType seedRaw targetType targetRaw seedRank targetRank hs ht hsr htr had hl hm
 have hall := GenericPrimaryProof.preserved OriginalRawSyntaxTransport.variableRankPackedRaw
   (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
   (SeededPrimaryPool.pool
     (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
     (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)))
   (OriginalConcreteStructuralEdge.edge n arity) seed parameter out seedRank had hl hsr
   (ConcreteClosureProof.closed n arity seedRank parameter)
 have hr := InvariantProof.eliminate OriginalRawSyntaxTransport.variableRankPackedRaw seedRank out candidate hall hm
 exact valueUnique OriginalRawSyntaxTransport.variableRankPackedRaw seedRank targetRank (Fin.cons candidate Fin.elim0) hr htr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.Proof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationSwapDefinitions OriginalTypedArgumentObservations

open InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem observedAppend (R : Program 2) (front rawTail built parameter mappedFront tailValue out : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (graph2 OriginalTypedArgumentPrefixBuilder.build built front rawTail)))
 (hm : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentPrefixBuilder.mapped R) mappedFront front parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 (argumentObservations R) tailValue rawTail parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (argumentObservations R) out built parameter))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out mappedFront tailValue)) := by
 apply programCases InternalApplicationValidityStackAppend.append ![mappedFront,tailValue] _
 intro beta rho Theta total hrho ha
 rw [binaryVectorRename] at ha
 rw [graph2Rename]
 have hb' := renameInto hb rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 have ht' := renameInto ht rho Theta hrho
 have ho' := renameInto ho rho Theta hrho
 rw [graph2Rename] at hb' hm' ht' ho'
 have h := OriginalTypedArgumentPrefixBuilderProof.actualAppend R body beta Theta
   (front.relabel rho) (rawTail.relabel rho) (built.relabel rho) (parameter.relabel rho)
   (mappedFront.relabel rho) (tailValue.relabel rho) total hb' hm' ht' ha
 have he := valueUnique (argumentObservations R) total (out.relabel rho)
   (Fin.cons (built.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)) h ho'
 exact outputTransport InternalApplicationValidityStackAppend.append total (out.relabel rho)
   (Fin.cons (mappedFront.relabel rho) (Fin.cons (tailValue.relabel rho) Fin.elim0)) he ha

theorem actualAdjacent : OriginalTypedArgumentPrefixAdjacentTargets.ActualAdjacent := by
 intro R body alpha Delta sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate front mappedFront builtSource builtTarget finalSource finalTarget finalCertificate hg hc ho hk hbSource hbTarget hm hSource hTarget hCertificate
 have he := OriginalTypedArgumentObservationSwapProof.actualAt R sigma tau q r rawTail rawY rawX sourceRaw targetRaw packedQ packedR valueQ valueR typedQ typedR parameter observedTail source target rest payload certificate hg hc ho hk
 have hs := observedAppend R front sourceRaw builtSource parameter mappedFront source finalSource
   hbSource hm (andLeft (andRight ho)) hSource
 have ht := observedAppend R front targetRaw builtTarget parameter mappedFront target finalTarget
   hbTarget hm (andRight (andRight ho)) hTarget
 exact OriginalNumericListSortExchangeZeroPrefixProof.extend source target certificate payload mappedFront finalCertificate finalSource finalTarget
   he (andRight (andRight hk)) hCertificate hs ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentProof

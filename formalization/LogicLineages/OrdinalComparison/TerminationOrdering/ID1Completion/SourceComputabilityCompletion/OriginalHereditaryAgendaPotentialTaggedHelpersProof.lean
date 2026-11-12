module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalListCodecSupportProof (consGraph)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalAdditionLawsProof (add)
open OriginalHereditaryAgendaPotential
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceBranchProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraphRename)
open InternalTagArithmeticSyntaxProof (zRelabel)

theorem tagNil : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits z z)) :=
 InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 0 0)
   OriginalHereditaryVisitScheduler.tagStep z Fin.elim0
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 Fin.elim0)

theorem tagConsValue (jobs head tail tagged visit taggedTail : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z head)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits taggedTail tail)))
 (ho : Nonempty (Derivation body Delta (consGraph tagged visit taggedTail))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons head (Fin.cons taggedTail Fin.elim0)
 apply InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 0 0)
   OriginalHereditaryVisitScheduler.tagStep jobs head tail taggedTail tagged Fin.elim0 hc ht
 exact binaryValue InternalListCodec.consCode
   (pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)) (.projection 1)
   tagged visit taggedTail xs ho
   (binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
     visit z head xs hv (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xs) (projectionValue 0 xs))
   (projectionValue 1 xs)

theorem tagCons (jobs head tail tagged visit taggedTail : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z head)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits taggedTail tail)))
 (ho : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs))) :
 Nonempty (Derivation body Delta (consGraph tagged visit taggedTail)) := by
 apply programCases InternalListCodec.consCode (Fin.cons visit (Fin.cons taggedTail Fin.elim0)) _
 intro beta j Theta fresh hj hf
 simp only [consTermRename,emptyRename] at hf
 have hc' := renameInto hc j Theta hj
 have hv' := renameInto hv j Theta hj
 have ht' := renameInto ht j Theta hj
 have ho' := renameInto ho j Theta hj
 simp only [consGraphRename,graph2Rename,graph1Rename,zRelabel] at hc' hv' ht' ho'
 rw [consGraphRename]
 have htag := tagConsValue (jobs.relabel j) (head.relabel j) (tail.relabel j) fresh
   (visit.relabel j) (taggedTail.relabel j) hc' hv' ht' hf
 exact outputTransport InternalListCodec.consCode fresh (tagged.relabel j)
   (Fin.cons (visit.relabel j) (Fin.cons (taggedTail.relabel j) Fin.elim0))
   (valueUnique OriginalHereditaryVisitScheduler.tagVisits fresh (tagged.relabel j)
     (Fin.cons (jobs.relabel j) Fin.elim0) htag ho') hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobArityRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobRawPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAnnotationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof (projectionValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withoutAnnotations
 (firstOne : OriginalInternalJobChildCasesTargets.ActualCases true 1)
 (firstTwo : OriginalInternalJobChildCasesTargets.ActualCases true 2)
 (second : OriginalInternalJobChildCasesTargets.ActualCases false 2)
 (H : Program 1) (M W : Program 2)
 (index role typ raw rawCell parameter gamma c child childRole childType typed stored childRaw childParameter childGamma jobs count : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hexp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count jobs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell index jobs)))
 (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma))) :
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 apply programCases InternalPairing.pairing (Fin.cons role (Fin.cons typ Fin.elim0)) _
 intro beta j Theta inherited hj hinherit
 rw [admissibleRename]
 simp only [consTermRename,emptyRename] at hinherit
 have ha' := renameInto ha j Theta hj
 have hp' := renameInto hp j Theta hj
 have hexp' := renameInto hexp j Theta hj
 have hl' := renameInto hl j Theta hj
 have hb' := renameInto hb j Theta hj
 have hlookup' := renameInto hlookup j Theta hj
 have hd' := renameInto hd j Theta hj
 have hcp' := renameInto hcp j Theta hj
 have ht' := renameInto ht j Theta hj
 have hcr' := renameInto hcr j Theta hj
 have hcg' := renameInto hcg j Theta hj
 simp only [admissibleRename,graph1Rename,graph2Rename,graph5Rename,OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at ha' hp' hexp' hl' hb' hlookup' hd' hcp' ht' hcr' hcg'
 apply programCases InternalPairing.pairing (Fin.cons (childRole.relabel j) (Fin.cons (childType.relabel j) Fin.elim0)) _
 intro gammaType k Xi annotation hk hann
 rw [admissibleRename]
 simp only [consTermRename,emptyRename] at hann
 have ha'' := renameInto ha' k Xi hk
 have hp'' := renameInto hp' k Xi hk
 have hexp'' := renameInto hexp' k Xi hk
 have hl'' := renameInto hl' k Xi hk
 have hb'' := renameInto hb' k Xi hk
 have hlookup'' := renameInto hlookup' k Xi hk
 have hd'' := renameInto hd' k Xi hk
 have hcp'' := renameInto hcp' k Xi hk
 have ht'' := renameInto ht' k Xi hk
 have hcr'' := renameInto hcr' k Xi hk
 have hcg'' := renameInto hcg' k Xi hk
 have hinherit'' := renameInto hinherit k Xi hk
 simp only [admissibleRename,graph1Rename,graph2Rename,graph5Rename,OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at ha'' hp'' hexp'' hl'' (by simpa only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.ltF] using hb'') hlookup'' hd'' hcp'' ht'' hcr'' hcg'' hinherit''
 exact OriginalInternalJobRawPreservationProof.rawPreservation firstOne firstTwo second H M W
  ((index.relabel j).relabel k) ((role.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) ((rawCell.relabel j).relabel k) ((parameter.relabel j).relabel k) ((gamma.relabel j).relabel k) ((c.relabel j).relabel k) ((child.relabel j).relabel k) ((childRole.relabel j).relabel k) ((childType.relabel j).relabel k) ((typed.relabel j).relabel k) ((stored.relabel j).relabel k) annotation ((childRaw.relabel j).relabel k) ((childParameter.relabel j).relabel k) ((childGamma.relabel j).relabel k) (inherited.relabel k) ((jobs.relabel j).relabel k) ((count.relabel j).relabel k)
  ha'' hp'' hexp'' hl'' (by simpa only [OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.ltF] using hb'') hlookup'' hinherit'' hd'' hcp'' ht'' hann hcr'' hcg''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAnnotationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAnnotationsProof

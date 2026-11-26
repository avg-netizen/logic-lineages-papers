module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildMetadataCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket OriginalInternalJobChildCasesTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem ordinaryFirstCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma head base : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalJobChildQueriesProof.metadataCases H head raw psi
 intro beta j Theta data result types payload annotation hinc hh ht hright hann
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 simp only [graph2Rename] at hc'
 let xs : Fin 1 → OTerm beta := ![raw.relabel j]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.ordinaryTag (.projection 0) (raw.relabel j) (head.relabel j) (base.relabel j) xs (projectionValue 0 xs) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 4) payload (unaryRecover InternalUnpair.left (.projection 0) (numeral 4) (raw.relabel j) xs htag (projectionValue 0 xs)) hright
 have packet := OriginalInternalJobChildFieldsProof.ordinaryFirst H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) payload (head.relabel j) (base.relabel j)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) data result types annotation hc' hraw hp' hj' hh ht hann ha'
 exact next beta j Theta (numeral 1) (numeral 0) (base.relabel j) (gamma.relabel j) (parameter.relabel j) annotation hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
theorem numberedFirstCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma label head recorded base extraTypes extras : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalJobChildQueriesProof.metadataCases H head raw psi
 intro beta j Theta data result types payload annotation hinc hh ht hright hann
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 simp only [programRename,OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename] at hc'
 let xs : Fin 1 → OTerm beta := ![raw.relabel j]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag (.projection 0) (raw.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) xs (projectionValue 0 xs) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 5) payload (unaryRecover InternalUnpair.left (.projection 0) (numeral 5) (raw.relabel j) xs htag (projectionValue 0 xs)) hright
 have packet := OriginalInternalJobChildFieldsProof.numberedFirst H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) payload (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) data result types annotation hc' hraw hp' hj' hh ht hann ha'
 exact next beta j Theta (numeral 1) (numeral 0) (base.relabel j) (gamma.relabel j) (parameter.relabel j) annotation hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
theorem numberedSecondCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma label head recorded base extraTypes extras : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalInternalJobChildQueriesProof.metadataCases H head raw psi
 intro beta j Theta data result types payload annotation hinc hh ht hright hann
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 simp only [programRename,OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename] at hc'
 let xs : Fin 1 → OTerm beta := ![raw.relabel j]
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag (.projection 0) (raw.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) xs (projectionValue 0 xs) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 5) payload (unaryRecover InternalUnpair.left (.projection 0) (numeral 5) (raw.relabel j) xs htag (projectionValue 0 xs)) hright
 have packet := OriginalInternalJobChildFieldsProof.numberedSecond H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) payload (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) data result types annotation hc' hraw hp' hj' hh ht hann ha'
 exact next beta j Theta (numeral 1) (numeral 0) (extras.relabel j) (gamma.relabel j) (parameter.relabel j) annotation hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildMetadataCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildMetadataCasesProof

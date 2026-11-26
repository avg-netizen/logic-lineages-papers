module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildMetadataCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTagCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket OriginalInternalJobChildCasesTargets
open OriginalRawSyntaxTransportInternalParserSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lambdaFirst (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases raw psi ht
 intro beta j Theta domain child hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildLambdaCasesProof.lambdaFirstCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  domain child (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 0) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem ordinaryFirst (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases raw psi ht
 intro beta j Theta head child hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildMetadataCasesProof.ordinaryFirstCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  head child (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 0) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem applicationFirst (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw psi ht
 intro beta j Theta domain fn arg hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildApplicationCasesProof.applicationFirstCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  domain fn arg (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 0) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem applicationSecond (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw psi ht
 intro beta j Theta domain fn arg hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildApplicationCasesProof.applicationSecondCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  domain fn arg (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 1) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem numberedFirst (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw psi ht
 intro beta j Theta label head recorded base extraTypes extras hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildMetadataCasesProof.numberedFirstCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  label head recorded base extraTypes extras (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 0) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem numberedSecond (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw psi ht
 intro beta j Theta label head recorded base extraTypes extras hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildMetadataCasesProof.numberedSecondCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  label head recorded base extraTypes extras (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 1) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem consFirst (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw psi ht
 intro beta j Theta domain head tail hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildConsCasesProof.consFirstCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  domain head tail (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 0) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
theorem consSecond (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalRawSyntaxTransportInternalParserBinaryProof.consCases raw psi ht
 intro beta j Theta domain head tail hinc hc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 apply OriginalInternalJobChildConsCasesProof.consSecondCases H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
  domain head tail (psi.relabel j) hc ha' hp' hj'
 have hn := OriginalInternalJobChildCasesContextProof.consumerRename H M W
  (numeral 1) role typ raw cell parameter c gamma psi next j Theta hinc
 simpa only [GuardedSourceSyntaxProof.numeralRename] using hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTagCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTagCasesProof

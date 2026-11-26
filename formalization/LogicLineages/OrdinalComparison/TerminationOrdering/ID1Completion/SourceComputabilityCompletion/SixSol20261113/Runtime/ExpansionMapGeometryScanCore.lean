module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanRowSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm addZero addSucc)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion (lengthGraph)
open ExpansionMapGeometryScanDefinitions ExpansionMapGeometryScanSyntax ExpansionMapGeometryScanRowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroCore (start role typ raw jobs prefixRow full : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefixRow start role typ raw jobs)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start z) role typ raw jobs))) :
 Nonempty (Derivation body Delta (Extension z prefixRow full)) := by
 have hf' := headTransport OriginalHereditaryAnnotatedExpansion.scan full (add start z) start
   ![role,typ,raw,jobs] ⟨addZero start⟩ hf
 have he := valueUnique OriginalHereditaryAnnotatedExpansion.scan prefixRow full ![start,role,typ,raw,jobs] hp hf'
 have ha := SixSol20261112.Context.AppendIdentityProof.actualRightZero body alpha Delta prefixRow
 have h := outputTransport InternalApplicationValidityStackAppend.append prefixRow full ![prefixRow,z] he ha
 exact extensionIntro z prefixRow full z (andIntro OriginalContextInsertionLengthProof.lengthZero h)

theorem atValues (count start role typ raw jobs prefixRow full previous suffix mark single grown rawChild : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan previous (add start count) role typ raw jobs)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start (suc count)) role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count suffix)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append previous prefixRow suffix)))
 (hm : Nonempty (Derivation body Delta (graph5 OriginalHereditaryInternalAnnotatedScanDefinitions.cell mark (add start count) role typ raw jobs)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode single mark z)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append grown suffix single)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild (add start count) jobs))) :
 Nonempty (Derivation body Delta (Extension (suc count) prefixRow full)) := by
 have hf' := headTransport OriginalHereditaryAnnotatedExpansion.scan full (add start (suc count)) (suc (add start count))
   ![role,typ,raw,jobs] ⟨addSucc start count⟩ hf
 have happ := SixSol20261113.Context.NarrowScanAppendProof.scanAppendAtLookup
   (add start count) previous role typ raw jobs mark single full rawChild hp hf' hm hs hr
 have hout := SixSol20261112.Runtime.AppendReassociationProof.appendReassociation body alpha Delta
   prefixRow suffix single previous grown full ha hg happ
 have hlen := OriginalHereditaryDeletionRowsLengthProof.appendSingletonLength count suffix mark single grown hl hs hg
 exact extensionIntro (suc count) prefixRow full grown (andIntro hlen hout)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanCore

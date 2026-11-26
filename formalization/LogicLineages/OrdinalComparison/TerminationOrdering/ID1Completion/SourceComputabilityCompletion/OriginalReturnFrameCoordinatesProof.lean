module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualCoordinates : OriginalReturnFrameCoordinatesTargets.ActualCoordinates := by
 intro body alpha Delta input work results frame rest tag payload parent counts role typed rawJob typ raw parameter children deletions packed hstate hframe hpayload hparent htyped hrawJob hcounts hpacked hcons
 let xs : Fin 1 → OTerm alpha := ![input]
 have hi : Nonempty (Derivation body Delta (graph1 (.projection 0) input input)) := projectionValue 0 xs
 have hworkGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.work) work input)) :=
  unaryValue InternalUnpair.left (.projection 0) work input xs (pairLeft input work results hstate) hi
 have hresultsGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.results) results input)) :=
  unaryValue InternalUnpair.right (.projection 0) results input xs (pairRight input work results hstate) hi
 have hframeGraph : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.frame frame input)) :=
  unaryValue InternalListCodec.headCode OriginalHereditaryReturnStep.work frame work xs
   (InternalRawListRecursionSupportProof.consHead work frame rest hcons) hworkGraph
 have hpayloadGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.payload) payload input)) :=
  unaryValue InternalUnpair.right (OriginalHereditaryReturnStep.frame) payload frame xs (pairRight frame tag payload hframe) hframeGraph
 have hparentGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.parent) parent input)) :=
  unaryValue InternalUnpair.left (OriginalHereditaryReturnStep.payload) parent payload xs (pairLeft payload parent counts hpayload) hpayloadGraph
 have hcountsGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.counts) counts input)) :=
  unaryValue InternalUnpair.right (OriginalHereditaryReturnStep.payload) counts payload xs (pairRight payload parent counts hpayload) hpayloadGraph
 have hroleGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.role) role input)) :=
  unaryValue InternalUnpair.left (OriginalHereditaryReturnStep.parent) role parent xs (pairLeft parent role typed hparent) hparentGraph
 have htypedGraph : Nonempty (Derivation body Delta (graph1 (rightOf OriginalHereditaryReturnStep.parent) typed input)) :=
  unaryValue InternalUnpair.right (OriginalHereditaryReturnStep.parent) typed parent xs (pairRight parent role typed hparent) hparentGraph
 have hexpectedTypeGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.expectedType) typ input)) :=
  unaryValue InternalUnpair.left (rightOf OriginalHereditaryReturnStep.parent) typ typed xs (pairLeft typed typ rawJob htyped) htypedGraph
 have hrawJobGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.rawJob) rawJob input)) :=
  unaryValue InternalUnpair.right (rightOf OriginalHereditaryReturnStep.parent) rawJob typed xs (pairRight typed typ rawJob htyped) htypedGraph
 have hrawGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.raw) raw input)) :=
  unaryValue InternalUnpair.left (OriginalHereditaryReturnStep.rawJob) raw rawJob xs (pairLeft rawJob raw parameter hrawJob) hrawJobGraph
 have hparameterGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.parameter) parameter input)) :=
  unaryValue InternalUnpair.right (OriginalHereditaryReturnStep.rawJob) parameter rawJob xs (pairRight rawJob raw parameter hrawJob) hrawJobGraph
 have hchildCountGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.childCount) children input)) :=
  unaryValue InternalUnpair.left (OriginalHereditaryReturnStep.counts) children counts xs (pairLeft counts children deletions hcounts) hcountsGraph
 have hdeletionCountGraph : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.deletionCount) deletions input)) :=
  unaryValue InternalUnpair.right (OriginalHereditaryReturnStep.counts) deletions counts xs (pairRight counts children deletions hcounts) hcountsGraph
 have hpackedGraph : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.packed packed input)) :=
  binaryValue InternalPairing.pairing OriginalHereditaryReturnStep.expectedType OriginalHereditaryReturnStep.raw
   packed typ raw xs hpacked hexpectedTypeGraph hrawGraph
 obtain ⟨drole⟩ := hroleGraph
 obtain ⟨dexpectedType⟩ := hexpectedTypeGraph
 obtain ⟨draw⟩ := hrawGraph
 obtain ⟨dparameter⟩ := hparameterGraph
 obtain ⟨dchildCount⟩ := hchildCountGraph
 obtain ⟨ddeletionCount⟩ := hdeletionCountGraph
 obtain ⟨dpacked⟩ := hpackedGraph
 obtain ⟨dresults⟩ := hresultsGraph
 exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction (drole) dexpectedType) draw) dparameter) dchildCount) ddeletionCount) dpacked) dresults⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof

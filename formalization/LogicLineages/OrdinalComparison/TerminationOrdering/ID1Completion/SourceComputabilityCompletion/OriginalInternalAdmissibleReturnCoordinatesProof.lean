module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem coordinates
 (input work results frame rest tag payload parent counts role typed rawJob typ raw parameter : OTerm alpha)
 (hstate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame tag payload)))
 (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload parent counts)))
 (hparent : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)))
 (htyped : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hrawJob : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hcons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role role input ⊓ graph1 OriginalHereditaryReturnStep.raw raw input)) := by
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
 exact andIntro hroleGraph hrawGraph
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnCoordinatesProof

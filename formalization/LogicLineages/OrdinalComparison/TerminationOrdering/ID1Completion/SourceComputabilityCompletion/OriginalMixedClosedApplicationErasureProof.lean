module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedCongruenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceErasedValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointFrameProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)

theorem actualAtCoordinates : OriginalMixedClosedApplicationErasureTargets.ActualAtCoordinates := by
 intro H G M W oldStep window body alpha Delta oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newChildS newChildT newArg newParam erasedType cutoff gamma extended context hctor hh hparent hrec hi hop hnp hes het hecs hect hea ih
 have hs := andLeft hh
 have happS := andLeft (andRight hh)
 have happT := andLeft (andRight (andRight hh))
 have harrow := andLeft (andRight (andRight (andRight hh)))
 have htypeS := andLeft (andRight (andRight (andRight (andRight hh))))
 have htypeT := andLeft (andRight (andRight (andRight (andRight (andRight hh)))))
 have htypeA := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hsourceChild := andLeft (OriginalPackedSourceApplicationFieldsProof.sourceChildren H G M W
  arrow domain codomain fp ap oldChildS oldArg oldS oldParam hctor hs)
 have hchild : Nonempty (Derivation body Delta (graph4 (leaf H G M W oldStep) (numeral 1) oldChildS oldChildT oldChildCert oldParam)) := by
  obtain ⟨law⟩ := OriginalTransparentMixedPathApplicationPrefixProof.hop (source H G M W)
   (OriginalTransparentDirectBottom.refined (source H G M W) oldStep)
   oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow (numeral 1) hh
  obtain ⟨hparent⟩ := hparent
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft law) hparent⟩
 have hsourceE := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
  oldS newS erasedType cutoff gamma extended context oldParam newParam hi hes hop hnp hs
 have newAppS := OriginalPackedApplicationErasureProof.applicationErasure oldS domain codomain oldChildS oldArg
  newS newChildS newArg erasedType cutoff happS hes hecs hea
 have newAppT := OriginalPackedApplicationErasureProof.applicationErasure oldT domain codomain oldChildT oldArg
  newT newChildT newArg erasedType cutoff happT het hect hea
 have newTypeS := OriginalPackedApplicationErasureProof.eraseTypeCopy oldChildS newChildS arrow erasedType cutoff htypeS hecs
 have newTypeT := OriginalPackedApplicationErasureProof.eraseTypeCopy oldChildT newChildT arrow erasedType cutoff htypeT hect
 have newTypeA := OriginalPackedApplicationErasureProof.eraseTypeCopy oldArg newArg domain erasedType cutoff htypeA hea
 have frame : Nonempty (Derivation body Delta (OriginalMixedExistentialCongruenceDefinitions.ApplicationFrame
  (source H G M W) newS newT newParam newChildS newChildT newArg domain codomain arrow)) :=
  andIntro hsourceE (andIntro newAppS (andIntro newAppT (andIntro harrow (andIntro newTypeS (andIntro newTypeT newTypeA)))))
 have childResult := ih alpha id Delta
  (fun f hf => by simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using hf)
  newChildS newChildT newParam gamma extended
  (by simpa only [Term.relabel_id,OriginalTransparentMixedDirectBottom.source] using hsourceChild)
  (by simpa only [Term.relabel_id] using hchild)
  (by simpa only [Term.relabel_id] using hop)
  (by simpa only [Term.relabel_id] using hnp)
  (by simpa only [Term.relabel_id] using hi)
  (by simpa only [Term.relabel_id] using hecs)
  (by simpa only [Term.relabel_id] using hect)
 have both := OriginalMixedTraceErasedValidityProof.actualBothErasedSource H G M W oldStep body alpha Delta
  oldChildS oldChildT oldChildCert oldParam newParam gamma extended erasedType cutoff context newChildS newChildT
  (by simpa only [OriginalTransparentMixedDirectBottom.source] using hsourceChild) hrec hi hop hnp hecs hect
 have hend := OriginalMixedLiteralEndpointFrameProof.atFrame H G M W newS newT newParam newChildS newChildT newArg domain codomain arrow frame (andRight both)
 apply OriginalMixedClosedCongruenceApplicationProof.actualApplication H G M W oldStep window body alpha Delta
  newS newT newParam newChildS newChildT newArg domain codomain arrow oldS oldT oldChildS oldChildT oldArg
  frame hend happS happT
 simpa only [Term.relabel_id] using childResult
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnSupplierProof (Supplier)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem termFrame (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced
  first second row packed root returned tail value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hroot : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)))
 (hreturned : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed first second)))
 (htail : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)))
 (hvalue : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value root tail)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)) := by
 apply UniformReturnStepProof.frameFromReturn R frame payload produced value hf
 intro beta j Theta suffix old work results input pushed output hi hg
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have hroot' := renameInto hroot j Theta hi
 have hreturned' := renameInto hreturned j Theta hi
 have htail' := renameInto htail j Theta hi
 have hvalue' := renameInto hvalue j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' hpacked' hroot' hreturned' htail' hvalue'
 have hwork := andLeft hg
 have happend := andLeft (andRight hg)
 have hinput := andLeft (andRight (andRight hg))
 have hpushed := andLeft (andRight (andRight (andRight hg)))
 have houtput := andRight (andRight (andRight (andRight hg)))
 have hcoords := OriginalReturnFrameCoordinatesProof.actualCoordinates body beta Theta input work results
   (frame.relabel j) suffix (numeral 1) (payload.relabel j) (job.relabel j) (counts.relabel j)
   (numeral 0) (typed.relabel j) (rawJob.relabel j) (typ.relabel j) (raw.relabel j)
   (parameter.relabel j) (children.relabel j) (deletions.relabel j) (packed.relabel j)
   hinput hf' hp' hj' ht' hr' hc' hpacked' hwork
 have hrole := (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hcoords)))))))
 have hparameter := (andRight (andLeft (andLeft (andLeft (andLeft hcoords)))))
 have hchildren := (andRight (andLeft (andLeft (andLeft hcoords))))
 have hdeletions := (andRight (andLeft (andLeft hcoords)))
 have hpack := (andRight (andLeft hcoords))
 have hresults := (andRight hcoords)
 have hselectors := hs beta j Theta old results hi happend
 have hfirst := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.firstSlot
   input (children.relabel j) (deletions.relabel j) results (first.relabel j)
   hchildren hdeletions hresults (andLeft hselectors)
 have hsecond := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.secondSlot
   input (children.relabel j) (deletions.relabel j) results (second.relabel j)
   hchildren hdeletions hresults (andLeft (andRight hselectors))
 have hrow := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.deletionRow
   input (children.relabel j) (deletions.relabel j) results (row.relabel j)
   hchildren hdeletions hresults (andLeft (andRight (andRight hselectors)))
 have hold := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.oldSuffix
   input (children.relabel j) (deletions.relabel j) results old
   hchildren hdeletions hresults (andRight (andRight (andRight hselectors)))
 exact OriginalHereditaryReturnStepInternalTermProof.termLaw R body beta Theta
   input work results (frame.relabel j) suffix (payload.relabel j) (packed.relabel j)
   (parameter.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) old
   (root.relabel j) (returned.relabel j) (tail.relabel j) (value.relabel j) pushed output
   hinput hwork hf' hrole hpack hparameter hfirst hsecond hrow hold
   hroot' hreturned' htail' hvalue' hpushed houtput
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermFrameProof

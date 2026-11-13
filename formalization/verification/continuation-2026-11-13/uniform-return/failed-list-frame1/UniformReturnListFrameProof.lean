module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalListConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListFrameProof
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
theorem nilFrame (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced
  first second row packed rawPayload : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced (numeral 0))) := by
 apply UniformReturnStepProof.frameFromReturn R frame payload produced (numeral 0) hf
 intro beta j Theta suffix old work results input pushed output hi hg
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have htag' := renameInto htag j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at htag' hj' ht' hr' hc' hp' hf' hpacked'
 have hwork := andLeft hg
 have happend := andLeft (andRight hg)
 have hinput := andLeft (andRight (andRight hg))
 have hpushed := andLeft (andRight (andRight (andRight hg)))
 have houtput := andRight (andRight (andRight (andRight hg)))
 have hcoords := OriginalReturnFrameCoordinatesProof.actualCoordinates body beta Theta input work results
   (frame.relabel j) suffix (numeral 1) (payload.relabel j) (job.relabel j) (counts.relabel j)
   (numeral 1) (typed.relabel j) (rawJob.relabel j) (typ.relabel j) (raw.relabel j)
   (parameter.relabel j) (children.relabel j) (deletions.relabel j) (packed.relabel j)
   hinput hf' hp' hj' ht' hr' hc' hpacked' hwork
 have hrole := andLeft hcoords
 have hraw := andLeft (andRight (andRight hcoords))
 have hchildren := andLeft (andRight (andRight (andRight (andRight hcoords))))
 have hdeletions := andLeft (andRight (andRight (andRight (andRight (andRight hcoords)))))
 have hresults := andRight (andRight (andRight (andRight (andRight (andRight (andRight hcoords))))))
 have hselectors := hs beta j Theta old results hi happend
 have hold := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.oldSuffix
   input (children.relabel j) (deletions.relabel j) results old
   hchildren hdeletions hresults (andRight (andRight (andRight hselectors)))
 exact OriginalHereditaryReturnStepInternalListNilProof.listNilLaw R body beta Theta
   input work results (frame.relabel j) suffix (payload.relabel j) (raw.relabel j) (rawPayload.relabel j)
   old pushed output hinput hwork hf' hrole hraw htag' hold
   (by simpa only [numeralRename] using hpushed) houtput

theorem consFrame (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced
  first second row packed rawPayload value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)))
 (hvalue : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons value raw first second)))
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
 have hvalue' := renameInto hvalue j Theta hi
 have htag' := renameInto htag j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at htag' hj' ht' hr' hc' hp' hf' hpacked' hvalue'
 have hwork := andLeft hg
 have happend := andLeft (andRight hg)
 have hinput := andLeft (andRight (andRight hg))
 have hpushed := andLeft (andRight (andRight (andRight hg)))
 have houtput := andRight (andRight (andRight (andRight hg)))
 have hcoords := OriginalReturnFrameCoordinatesProof.actualCoordinates body beta Theta input work results
   (frame.relabel j) suffix (numeral 1) (payload.relabel j) (job.relabel j) (counts.relabel j)
   (numeral 1) (typed.relabel j) (rawJob.relabel j) (typ.relabel j) (raw.relabel j)
   (parameter.relabel j) (children.relabel j) (deletions.relabel j) (packed.relabel j)
   hinput hf' hp' hj' ht' hr' hc' hpacked' hwork
 have hrole := andLeft hcoords
 have hraw := andLeft (andRight (andRight hcoords))
 have hchildren := andLeft (andRight (andRight (andRight (andRight hcoords))))
 have hdeletions := andLeft (andRight (andRight (andRight (andRight (andRight hcoords)))))
 have hresults := andRight (andRight (andRight (andRight (andRight (andRight (andRight hcoords))))))
 have hselectors := hs beta j Theta old results hi happend
 have hold := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.oldSuffix
   input (children.relabel j) (deletions.relabel j) results old
   hchildren hdeletions hresults (andRight (andRight (andRight hselectors)))
 have hfirst := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.firstSlot
   input (children.relabel j) (deletions.relabel j) results (first.relabel j)
   hchildren hdeletions hresults (andLeft hselectors)
 have hsecond := OriginalRestoredTermReturnProof.selected OriginalHereditaryResultStackProgram.secondSlot
   input (children.relabel j) (deletions.relabel j) results (second.relabel j)
   hchildren hdeletions hresults (andLeft (andRight hselectors))
 exact OriginalHereditaryReturnStepInternalListConsProof.listConsLaw R body beta Theta
   input work results (frame.relabel j) suffix (payload.relabel j) (raw.relabel j) (rawPayload.relabel j)
   (first.relabel j) (second.relabel j) old (value.relabel j) pushed output
   hinput hwork hf' hrole hraw htag' hfirst hsecond hold hvalue' hpushed houtput

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListFrameProof

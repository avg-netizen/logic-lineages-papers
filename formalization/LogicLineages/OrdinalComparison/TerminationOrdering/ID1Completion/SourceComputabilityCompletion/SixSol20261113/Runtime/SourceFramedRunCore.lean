module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem runWithStates (R : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged count produced value
  input work old visit suffix returnRest next visitOutput results returnInput pushed output : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced)))
 (hreturn : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R returnFrame produced value)))
 (hg : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.geometry job value suffix old visit work input pushed output)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode returnRest returnFrame suffix)))
 (hnext : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append next tagged returnRest)))
 (hvisit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visitOutput next old)))
 (hresults : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
 (hinput : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnInput returnRest results)))
 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R)
    output (suc (add count (suc (numeral 0)))) input)) := by
 have hstep := SourceFramedVisitProof.visitStep R job role typed typ rawJob raw parameter c gamma children deletions counts
   payload returnFrame jobs tagged input work old visit suffix returnRest next visitOutput
   hj ht hr hp ha hl hc hpay hframe he htag (andLeft (andRight (andRight hg)))
   (andLeft (andRight hg)) (andLeft hg) hrest hnext hvisit
 have hchildren := PrefixFrameSyntax.frameApply R tagged count produced returnRest old next visitOutput results returnInput
   hprefix (andIntro hnext (andIntro hvisit (andIntro hresults hinput)))
 have hret := UniformReturnSyntax.frameApply R returnFrame produced value suffix old returnRest results returnInput pushed output
   hreturn (andIntro hrest (andIntro hresults (andIntro hinput
     (andIntro (andLeft (andRight (andRight (andRight hg)))) (andRight (andRight (andRight (andRight hg))))))))
 have hfused := InternalNumericIterationFusionProof.fusionValue (OriginalHereditaryCombinedStep.step R)
   count (suc (numeral 0)) visitOutput returnInput output hchildren hret
 exact InternalNumericIterationProof.frontSuccBackward (OriginalHereditaryCombinedStep.step R)
   (add count (suc (numeral 0))) output input visitOutput hstep hfused
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunCore

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildAdmissibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof OriginalHereditaryInternalAgendaBindingProof
open OriginalHereditaryInternalJobRow OriginalHereditaryInternalJobRowSyntaxProof OriginalHereditaryInternalJobRowBindingProof
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem childAtFields (H : Program 1) (M W : Program 2)
 (c B parent role typ typed rawJob raw parameter gamma weight row count index child
 childRole childType childTyped childRawJob childRaw childParameter childGamma childWeight : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (jobFields H M W c B parent role typ typed rawJob raw parameter gamma weight)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole childTyped)))
 (hct : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childTyped childType childRawJob)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childRawJob childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)))
 (hcw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight childWeight child))) :
 Nonempty (Derivation body Delta (Job H M W c B child)) := by
 have hp := andLeft hf
 have ht := andLeft (andRight hf)
 have hr := andLeft (andRight (andRight hf))
 have hparam := andLeft (andRight (andRight (andRight hf)))
 have ha := andLeft (andRight (andRight (andRight (andRight hf))))
 have hw := andLeft (andRight (andRight (andRight (andRight (andRight hf)))))
 have hbound := andRight (andRight (andRight (andRight (andRight (andRight hf)))))
 have haccept := SixSol20261113.Runtime.SourceFramedChildAdmissibilityProof.actualLookup body H M W alpha Delta
  parent role typ typed rawJob raw parameter gamma c child childRole childType childTyped childRawJob childRaw childParameter childGamma
  row count index hp ht hr hparam hcp hct hcr hcg ha he hl hb hk
 have hless := SixSol20261113.Runtime.SourceFramedChildDecreaseProof.actualLookupDecrease body alpha Delta parent row count index child weight childWeight he hl hb hk hw hcw
 have hs1 := InternalRecursionGraphExtensionSupportProof.successorOrder childWeight weight hless
 have hs2 := InternalRecursionGraphExtensionSupportProof.successorOrder (suc childWeight) (suc weight) hs1
 have hboundChild := InternalSquareRootArithmeticSupportProof.strictTrans (suc (suc childWeight)) (suc (suc weight)) (suc B) hs2 hbound
 exact jobIntro H M W c B child childRole childType childTyped childRawJob childRaw childParameter childGamma childWeight
  (andIntro hcp (andIntro hct (andIntro hcr (andIntro hcg (andIntro haccept (andIntro hcw hboundChild))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobProof

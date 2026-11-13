module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildMapRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalListCodecSupportProof (consGraph)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph scan decorate

theorem scanZero (role typ raw jobs : OTerm alpha) :
    Nonempty (Derivation body Delta (graph5 scan z z role typ raw jobs)) := by
  rw [graph5,scan]
  exact recursionZeroValue (InternalAcceptance.constantZero 4) scanStep z
    (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
    (InternalRawListRecursionSupportProof.constantZero _)

theorem atValues (F : Program 1)
    (role typ raw jobs annotatedPrefix row first resultTail second
      mark0 mark1 raw0 raw1 previous single0 single1 : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph5 scan annotatedPrefix (numeral 2) role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (consGraph row first resultTail)))
    (ht : Nonempty (Derivation body Delta (consGraph resultTail second z)))
    (hc0 : Nonempty (Derivation body Delta (graph5 cell mark0 z role typ raw jobs)))
    (hc1 : Nonempty (Derivation body Delta (graph5 cell mark1 (numeral 1) role typ raw jobs)))
    (hl0 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup raw0 z jobs)))
    (hl1 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup raw1 (numeral 1) jobs)))
    (hprev : Nonempty (Derivation body Delta (graph5 scan previous (numeral 1) role typ raw jobs)))
    (hs0 : Nonempty (Derivation body Delta (consGraph single0 mark0 z)))
    (hs1 : Nonempty (Derivation body Delta (consGraph single1 mark1 z))) :
    Nonempty (Derivation body Delta ((graph1 F first mark0) ⊓ (graph1 F second mark1))) := by
  have ha0 := NarrowScanAppendProof.scanAppendAtLookup z z role typ raw jobs mark0 single0 previous raw0
    (scanZero role typ raw jobs) hprev hc0 hs0 hl0
  have he := InternalApplicationValidityStackAppendListProof.appendZeroRecover previous single0 ha0
  obtain ⟨he⟩ := he
  have hprevious := outputTransport InternalListCodec.consCode single0 previous
    (Fin.cons mark0 (Fin.cons z Fin.elim0)) ⟨InternalTagArithmeticSupportProof.symm he⟩ hs0
  have ha1 := NarrowScanAppendProof.scanAppendAtLookup (numeral 1) previous role typ raw jobs mark1 single1 annotatedPrefix raw1
    hprev hp hc1 hs1 hl1
  have hpcons := InternalApplicationValidityStackAppendListProof.consForward previous mark0 z single1 single1 annotatedPrefix
    hprevious (InternalApplicationValidityStackAppendListProof.appendZeroValue single1) ha1
  have hm0 := ChildMapRecoverProof.recover F annotatedPrefix mark0 single1 first resultTail row hpcons hr hm
  have hm1 := ChildMapRecoverProof.recover F single1 mark1 z second z resultTail hs1 ht (andRight hm0)
  exact andIntro (andLeft hm0) (andLeft hm1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanCoreProof

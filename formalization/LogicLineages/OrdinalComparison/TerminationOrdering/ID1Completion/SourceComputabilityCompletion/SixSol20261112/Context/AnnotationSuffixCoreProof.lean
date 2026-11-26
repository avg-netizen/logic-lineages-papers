module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.MapAppendCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (refl symm trans addZero addSucc)
open InternalAdditionLawsProof (add congAddLeft leftSuccessor)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion (lengthGraph)
open OriginalContextInsertionLengthProof (lengthNilRecover)
open OriginalContextInsertionSupportProof (binaryInputs)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open AnnotationSuffixSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map OriginalHereditaryAnnotatedExpansion.scan
  InternalApplicationValidityStackAppend.append OriginalContextInsertion.length

theorem zeroCore (arity : Nat) (offset typ raw front jobs annotatedFront count full mapped : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields arity z offset typ raw front jobs annotatedFront count full mapped))) :
    Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append full annotatedFront mapped)) := by
  let start := bump arity offset
  have hp := andLeft (andRight (andRight (andRight hf)))
  have hl := andLeft (andRight (andRight (andRight (andRight hf))))
  have hs := andLeft (andRight (andRight (andRight (andRight (andRight hf)))))
  have hm := andRight (andRight (andRight (andRight (andRight (andRight hf)))))
  obtain ⟨hc⟩ := lengthNilRecover count hl
  have he : Nonempty (Derivation body Delta (eqn (add start count) start)) :=
    ⟨trans (congAddLeft start hc) (addZero start)⟩
  have hs' := headTransport OriginalHereditaryAnnotatedExpansion.scan full (add start count) start
    ![z,typ,raw,jobs] he hs
  obtain ⟨hfull⟩ := valueUnique OriginalHereditaryAnnotatedExpansion.scan full annotatedFront
    ![start,z,typ,raw,jobs] hs' hp
  obtain ⟨hmapped⟩ := valueUnique (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob)
    mapped z ![z,typ] hm (MapAppendCoreProof.mapZero InheritedMapDefinitions.inheritedJob typ)
  have hz := AppendIdentityProof.actualRightZero body alpha Delta annotatedFront
  have ho := outputTransport InternalApplicationValidityStackAppend.append annotatedFront full ![annotatedFront,z] ⟨symm hfull⟩ hz
  exact binaryInputs InternalApplicationValidityStackAppend.append full annotatedFront z annotatedFront mapped
    ⟨refl annotatedFront⟩ ⟨symm hmapped⟩ ho

theorem headAtOffset (start front suffix jobs head tail : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph start front)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)))
    (hc : Nonempty (Derivation body Delta (consGraph suffix head tail))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup head start jobs)) := by
  have hshift := SuffixLookupProof.actualUnboundedSuffixLookup body alpha Delta start front suffix jobs z head hl ha
  have hhead := OriginalAllPositionContextDeleteBaseProof.lookupZero suffix head tail hc
  have hlook := OriginalTypedDecoderTransportLogicalProof.iffBackward hshift hhead
  exact headTransport InternalRawListRecursion.lookup head (add start z) start ![jobs] ⟨addZero start⟩ hlook

theorem grownRawAppend (front suffix jobs head tail singleton grown actual : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph suffix head tail)))
    (hs : Nonempty (Derivation body Delta (consGraph singleton head z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)))
    (hg : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append grown front singleton)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append actual grown tail))) :
    Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs grown tail)) := by
  have hsingle := InternalApplicationValidityStackAppendListProof.consBackward singleton head z tail tail suffix
    hs (InternalApplicationValidityStackAppendListProof.appendZeroValue tail) hc
  have hreassoc := Runtime.AppendReassociationProof.appendReassociation body alpha Delta
    front singleton tail grown suffix actual hg hsingle ht
  have he := valueUnique InternalApplicationValidityStackAppend.append actual jobs ![front,suffix] hreassoc ha
  exact outputTransport InternalApplicationValidityStackAppend.append actual jobs ![grown,tail] he ht

theorem countShift (start count tailCount : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn count (InternalTagArithmeticSyntaxProof.suc tailCount)))) :
    Nonempty (Derivation body Delta
      (eqn (add start count) (add (InternalTagArithmeticSyntaxProof.suc start) tailCount))) := by
  obtain ⟨he⟩ := he
  exact ⟨trans (congAddLeft start he)
    (trans (addSucc start tailCount) (symm (leftSuccessor start tailCount)))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixCoreProof

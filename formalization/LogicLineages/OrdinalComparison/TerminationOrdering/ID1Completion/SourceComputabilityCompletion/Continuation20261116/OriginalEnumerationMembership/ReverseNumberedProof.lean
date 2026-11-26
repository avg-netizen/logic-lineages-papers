module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NumberedMeaningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open MeaningSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

open InternalAcceptanceSupportProof (programCases)
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
open OriginalEnumerationDepth.BinaryValueProof (numberedRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalTypeListsMembership.MemberSyntaxProof (membersRename)

theorem atLength (n : Nat) (bound fuel types heads labels tupleBound prior raw label head typ base typeList extra len : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,base,typeList,extra])))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len typeList)))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.numberedCase n labels heads types tupleBound prior raw)) := by
  have hf := (NumberedMeaningProof.numbered n raw bound fuel types heads labels tupleBound label head typ base typeList extra hc).mp h
  have rest := andRight hf
  have hmetadata := andLeft (andLeft (andLeft rest))
  have hlabel := andLeft (andLeft hmetadata)
  have hhead := andRight (andLeft hmetadata)
  have htyp := andRight hmetadata
  have hbase := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound base hi).mpr
    (andRight (andLeft (andLeft rest)))
  have hextra := (ListBindingProof.atRaw n prior bound fuel types heads labels tupleBound extra hi).mpr (andRight rest)
  have htypes := andRight (andLeft rest)
  have hbound := OriginalEnumerationFields.Types.AllowedProof.lengthBound typeList types tupleBound len hlen htypes
  have hall := OriginalEnumerationFields.Types.AllowedProof.members typeList types tupleBound htypes
  apply OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof.cases (OriginalEncodedHeadConversion.convert n)
    heads head _ hhead
  intro beta j Theta encoded hj hmember hconvert
  rw [OriginalEnumerationLayerFields.NumberedSyntaxProof.caseRename]
  have hcj := renameInto hc j Theta hj
  rw [numberedRename] at hcj
  have hlabelj := renameInto hlabel j Theta hj
  have hboundj := renameInto hbound j Theta hj
  simp only [strictRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hlabelj hboundj
  have htypj := renameInto htyp j Theta hj
  have hbasej := renameInto hbase j Theta hj
  have hextraj := renameInto hextra j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at htypj hbasej hextraj
  have hlenj := renameInto hlen j Theta hj
  rw [lengthRename] at hlenj
  have hallj := renameInto hall j Theta hj
  rw [membersRename] at hallj
  exact OriginalEnumerationLayerFields.NumberedSyntaxProof.introduce n (labels.relabel j) (heads.relabel j)
    (types.relabel j) (tupleBound.relabel j) (prior.relabel j) (raw.relabel j)
    ![label.relabel j,encoded,head.relabel j,typ.relabel j,base.relabel j,typeList.relabel j,extra.relabel j,len.relabel j]
    (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro hlabelj hmember)
      hconvert) htypj) hbasej) hlenj) hboundj) hallj) hextraj) hcj)

theorem atConstructor (n : Nat) (bound fuel types heads labels tupleBound prior raw label head typ base typeList extra : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (Lists.Characterizes n prior bound fuel types heads labels tupleBound)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,base,typeList,extra])))
    (h : Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.numberedCase n labels heads types tupleBound prior raw)) := by
  apply programCases OriginalContextInsertion.length (Fin.cons typeList Fin.elim0) _
  intro beta j Theta len hj hlen
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hlen
  rw [OriginalEnumerationLayerFields.NumberedSyntaxProof.caseRename]
  have hcj := renameInto hc j Theta hj
  rw [numberedRename] at hcj
  have hij := renameInto hi j Theta hj
  rw [ListSyntaxProof.allRename] at hij
  have hmj := renameInto h j Theta hj
  simp only [meaningRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hmj
  exact atLength n (bound.relabel j) (fuel.relabel j) (types.relabel j) (heads.relabel j) (labels.relabel j)
    (tupleBound.relabel j) (prior.relabel j) (raw.relabel j) (label.relabel j) (head.relabel j) (typ.relabel j)
    (base.relabel j) (typeList.relabel j) (extra.relabel j) len hij hcj hlen hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ReverseNumberedProof

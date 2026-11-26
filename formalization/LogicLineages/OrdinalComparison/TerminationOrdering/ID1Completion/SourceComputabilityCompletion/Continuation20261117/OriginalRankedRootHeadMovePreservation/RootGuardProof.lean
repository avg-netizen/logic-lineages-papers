module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootFieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem ordinary (n : Nat) (raw head base : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) head ⊓
      graph1 (OriginalCodeValidityGuard.check n) (suc z) base)) := by
  apply Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardObservationProof.cases n raw _ hg
  intro beta j Theta tag payload first second hd hj hp hf _hs hh ha
  simp only [conjunctionRename,graph1Rename,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  obtain ⟨htk,hhk,hfk⟩ := RootFieldProof.ordinaryFields (raw.relabel j) (head.relabel j) (base.relabel j) hc'
  have hto := unaryValue InternalUnpair.left (.projection 0) tag (raw.relabel j) ![raw.relabel j]
    (pairLeft (raw.relabel j) tag payload hp) (projectionValue 0 ![raw.relabel j])
  have het := valueUnique (leftOf (.projection 0)) tag (numeral 4) ![raw.relabel j] hto htk
  have hav := RootAllowedProof.ordinary n tag payload first second hd het ha
  have heh := valueUnique (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) hd (head.relabel j)
    ![raw.relabel j] hh hhk
  have hef := valueUnique (firstOf (.projection 0)) first (base.relabel j) ![raw.relabel j] hf hfk
  exact andIntro (headTransport (OriginalHeadDecoderValidity.check n) (suc z) hd (head.relabel j) Fin.elim0 heh (andLeft hav))
    (headTransport (OriginalCodeValidityGuard.check n) (suc z) first (base.relabel j) Fin.elim0 hef (andRight hav))

theorem numbered (n : Nat) (raw label head recorded base extraTypes extras : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,recorded,base,extraTypes,extras])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) head ⊓
      graph1 (OriginalCodeValidityGuard.check n) (suc z) base)) := by
  apply Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardObservationProof.cases n raw _ hg
  intro beta j Theta tag payload first second hd hj hp hf _hs hh ha
  simp only [conjunctionRename,graph1Rename,sucRelabel,zRelabel]
  have hc' := renameInto hc j Theta hj
  simp only [programRename,OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename] at hc'
  obtain ⟨htk,hhk,hfk⟩ := RootFieldProof.numberedFields (raw.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) hc'
  have hto := unaryValue InternalUnpair.left (.projection 0) tag (raw.relabel j) ![raw.relabel j]
    (pairLeft (raw.relabel j) tag payload hp) (projectionValue 0 ![raw.relabel j])
  have het := valueUnique (leftOf (.projection 0)) tag (numeral 5) ![raw.relabel j] hto htk
  have hav := RootAllowedProof.numbered n tag payload first second hd het ha
  have heh := valueUnique (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) hd (head.relabel j)
    ![raw.relabel j] hh hhk
  have hef := valueUnique (firstOf (.projection 0)) first (base.relabel j) ![raw.relabel j] hf hfk
  exact andIntro (headTransport (OriginalHeadDecoderValidity.check n) (suc z) hd (head.relabel j) Fin.elim0 heh (andLeft hav))
    (headTransport (OriginalCodeValidityGuard.check n) (suc z) first (base.relabel j) Fin.elim0 hef (andRight hav))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootGuardProof

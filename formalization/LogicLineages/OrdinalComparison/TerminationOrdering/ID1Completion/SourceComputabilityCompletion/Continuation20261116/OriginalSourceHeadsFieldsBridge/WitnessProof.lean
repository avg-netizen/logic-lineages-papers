module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.CompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.WitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem introduce (n : Nat) (rawHead rawList heads encoded : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) rawHead)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) rawList rawHead)))
    (hmap : Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalHeadEncodingBridge.encodeHead) heads rawList)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead encoded rawHead))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n heads rawHead)) := by
  have hencoded := OriginalEncodedNumberedEnumerationBranch.MapIntroProof.introduce
    OriginalHeadEncodingBridge.encodeHead rawList z heads encoded z rawHead hmap hm he
  have hinverse := OriginalEncodedHeadConversion.Proof.internalInverse body alpha Delta n rawHead encoded hv he
  exact OriginalEncodedNumberedEnumerationBranch.MapImageProof.introduce
    (OriginalEncodedHeadConversion.convert n) heads rawHead encoded hencoded hinverse

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.WitnessProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherRankProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem initialValue (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output parameter rank : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 (minimumInputs p H G W P).base.oldRepresentative output input parameter)))
 (hi : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeafTupleProof.rawData (minimumInputs p H G W P) H G W).oldRepresentative
   output input parameter)) := by
 have hh := EvaluatorKeyOtherMinimumProof.minimumHit p H G W P input output parameter hd hm
 have ha := EvaluatorKeyOtherDomainProof.admitted p H G W input output parameter hd (andLeft hh) (andRight hh)
 have ho := EvaluatorKeyOtherRankProof.rankValue (baseRepresentative p H G W) H G (member p H G W) W
   input output parameter rank ha hi
 rw [OriginalAllPositionGuardedIndexedProof.initialRepresentative]
 exact ObservedOtherGuardProof.observedValue
   (OriginalRankGuardedRepresentative.active
     (OriginalTransparentDecoderSelection.transparentInputs H G W (minimumInputs p H G W P)).base.oldSource
     (minimumInputs p H G W P).window)
   (minimumInputs p H G W P).base.oldRepresentative
   OriginalRawSyntaxTransport.variableRankPackedRaw input output parameter rank (andRight hd) hm hi ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherGuardProof

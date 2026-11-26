module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atTransition (source : Program 2) (oldStep : Program 4)
 (xs ys : Fin 4 → OTerm alpha) (code head tail state next out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
 (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
 (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
 (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hs : Nonempty (Derivation body Delta (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state))) :
 Nonempty (Derivation body Delta ((programGraph (OriginalTransparentMixedPathDefinitions.refined source oldStep) out xs).iff
  (programGraph (OriginalTransparentMixedPathDefinitions.refined source oldStep) out ys))) := by
 let P := programGraph (OriginalTransparentMixedPathDefinitions.refined source oldStep) out xs
 let Q := programGraph (OriginalTransparentMixedPathDefinitions.refined source oldStep) out ys
 obtain ⟨hf⟩ := OriginalTransparentMixedPathRunProof.refinedForward source oldStep xs ys code head tail state next out
  (withHyp hp P) (withHyp ht P) (withHyp hl P) (withHyp hn P) (withHyp hc P) (withHyp hs P)
  (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨hb⟩ := OriginalTransparentMixedPathRunProof.refinedBackward source oldStep xs ys code head tail state next out
  (withHyp hp Q) (withHyp ht Q) (withHyp hl Q) (withHyp hn Q) (withHyp hc Q) (withHyp hs Q)
  (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualLambdaEquivalence : OriginalTransparentMixedPathCoordinateTargets.ActualLambdaEquivalence := by
 intro source oldStep body alpha Delta s t cert parameter childS childT childCert childParam d e context gamma extended code head tail state next out hh hp ht hl hn hc
 have hs := OriginalTransparentMixedPathLambdaProof.hop source s t cert parameter childS childT childCert childParam d e context gamma extended state next hh hl hn
 exact atTransition source oldStep ![s,t,cert,parameter] ![childS,childT,childCert,childParam]
  code head tail state next out hp ht hl hn hc hs

theorem actualApplicationEquivalence : OriginalTransparentMixedPathCoordinateTargets.ActualApplicationEquivalence := by
 intro source oldStep body alpha Delta s t cert parameter childS childT childCert arg d e arrow code head tail state next out hh hp ht hl hn hc
 have hs := OriginalTransparentMixedPathApplicationProof.hop source s t cert parameter childS childT childCert arg d e arrow state next hh hl hn
 exact atTransition source oldStep ![s,t,cert,parameter] ![childS,childT,childCert,parameter]
  code head tail state next out hp ht hl hn hc hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateProof

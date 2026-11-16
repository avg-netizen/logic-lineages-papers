module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryDepthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 DepthSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem forward (ordinary : Bool) (n : Nat) (raw metadata child fuel : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationDepth.UnaryProof.constructor ordinary) raw metadata child)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel)))) :
    Nonempty (Derivation body Delta (Targets.depthBound n child fuel)) := by
  apply programCases (OriginalEnumerationDepth.depth n) (Fin.cons child Fin.elim0) _
  intro beta j Theta d hj hd
  simp only [boundRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hd
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hbj := renameInto hb j Theta hj
  simp only [boundRename,sucRelabel] at hbj
  have hroot := OriginalEnumerationDepth.UnaryProof.value ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j) d hcj hvj hd
  have hbound := DepthBoundProof.observedBound n (raw.relabel j) (suc (fuel.relabel j)) (suc d) hroot hbj
  exact DepthBoundProof.introduce n (child.relabel j) (fuel.relabel j) d hd
    (OrderProof.successorBackward d (suc (fuel.relabel j)) hbound)

theorem backward (ordinary : Bool) (n : Nat) (raw metadata child fuel : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationDepth.UnaryProof.constructor ordinary) raw metadata child)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n child fuel))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel))) := by
  apply programCases (OriginalEnumerationDepth.depth n) (Fin.cons child Fin.elim0) _
  intro beta j Theta d hj hd
  simp only [boundRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hd
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hbj := renameInto hb j Theta hj
  simp only [boundRename,sucRelabel] at hbj
  have hroot := OriginalEnumerationDepth.UnaryProof.value ordinary n (raw.relabel j) (metadata.relabel j) (child.relabel j) d hcj hvj hd
  have hbound := DepthBoundProof.observedBound n (child.relabel j) (fuel.relabel j) d hd hbj
  exact DepthBoundProof.introduce n (raw.relabel j) (suc (fuel.relabel j)) (suc d) hroot
    (OrderProof.successorForward d (suc (fuel.relabel j)) hbound)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryDepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryDepthProof

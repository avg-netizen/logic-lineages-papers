module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryDepthProof
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

open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)

theorem forward (cons : Bool) (n : Nat) (raw typ left right fuel : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.BinaryValueProof.constructor cons) raw typ left right)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel)))) :
    Nonempty (Derivation body Delta (Targets.depthBound n left fuel ⊓ Targets.depthBound n right fuel)) := by
  apply OriginalEnumerationDepth.BinaryQueriesProof.cases n left right _
  intro beta j Theta dl dr maximum hj hdl hdr hm
  simp only [conjunctionRename,boundRename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hbj := renameInto hb j Theta hj
  simp only [conjunctionRename,boundRename,sucRelabel] at hbj
  have hroot := OriginalEnumerationDepth.BinaryValueProof.value cons n (raw.relabel j) (typ.relabel j)
    (left.relabel j) (right.relabel j) dl dr maximum hcj hvj hdl hdr hm
  have hbound := DepthBoundProof.observedBound n (raw.relabel j) (suc (fuel.relabel j)) (suc maximum) hroot hbj
  have hmax := OrderProof.successorBackward maximum (suc (fuel.relabel j)) hbound
  have hboth := MaximumProof.forward dl dr maximum (fuel.relabel j) hm hmax
  exact andIntro (DepthBoundProof.introduce n (left.relabel j) (fuel.relabel j) dl hdl (andLeft hboth))
    (DepthBoundProof.introduce n (right.relabel j) (fuel.relabel j) dr hdr (andRight hboth))

theorem backward (cons : Bool) (n : Nat) (raw typ left right fuel : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.BinaryValueProof.constructor cons) raw typ left right)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n left fuel ⊓ Targets.depthBound n right fuel))) :
    Nonempty (Derivation body Delta (Targets.depthBound n raw (suc fuel))) := by
  apply OriginalEnumerationDepth.BinaryQueriesProof.cases n left right _
  intro beta j Theta dl dr maximum hj hdl hdr hm
  simp only [conjunctionRename,boundRename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hbj := renameInto hb j Theta hj
  simp only [conjunctionRename,boundRename,sucRelabel] at hbj
  have hroot := OriginalEnumerationDepth.BinaryValueProof.value cons n (raw.relabel j) (typ.relabel j)
    (left.relabel j) (right.relabel j) dl dr maximum hcj hvj hdl hdr hm
  have hl := DepthBoundProof.observedBound n (left.relabel j) (fuel.relabel j) dl hdl (andLeft hbj)
  have hr := DepthBoundProof.observedBound n (right.relabel j) (fuel.relabel j) dr hdr (andRight hbj)
  have hmax := MaximumProof.backward dl dr maximum (fuel.relabel j) hm hl hr
  exact DepthBoundProof.introduce n (raw.relabel j) (suc (fuel.relabel j)) (suc maximum) hroot
    (OrderProof.successorForward maximum (suc (fuel.relabel j)) hmax)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryDepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryDepthProof

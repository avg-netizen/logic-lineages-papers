module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.DepthBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rightValue (a b : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess a b))) :
    Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum b a b)) :=
  successorBranchIntro InternalLessThan.ltTest (.projection 0) (.projection 1) b z ![a,b]
    (InternalLessThanSupportProof.acceptOfLess a b hl) (projectionValue 1 ![a,b])

theorem leftValue (a b : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess a b).not)) :
    Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum a a b)) :=
  zeroBranchIntro InternalLessThan.ltTest (.projection 0) (.projection 1) a ![a,b]
    (InternalLessThanSupportProof.rejectOfNotLess a b hl) (projectionValue 0 ![a,b])

theorem forward (a b m fuel : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum m a b)))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess m (suc fuel)))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess a (suc fuel) ⊓ InternalLessThan.strictLess b (suc fuel))) := by
  let L := InternalLessThan.strictLess a b
  apply formulaCases L
  · have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := valueUnique OriginalBoundsRecombination.maximum b m ![a,b] (rightValue a b hl) (withHyp hm L)
    have hbb := InternalOriginalPairingOrderArithmeticProof.strictTransport b (suc fuel) m (suc fuel) he ⟨refl _⟩ (withHyp hb L)
    exact andIntro (InternalSquareRootArithmeticSupportProof.strictTrans a b (suc fuel) hl hbb) hbb
  · have hl : Nonempty (Derivation body (L.not :: Delta) L.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := valueUnique OriginalBoundsRecombination.maximum a m ![a,b] (leftValue a b hl) (withHyp hm L.not)
    have hab := InternalOriginalPairingOrderArithmeticProof.strictTransport a (suc fuel) m (suc fuel) he ⟨refl _⟩ (withHyp hb L.not)
    exact andIntro hab (InternalOriginalPairingOrderArithmeticProof.weakStrictTrans b a (suc fuel)
      (InternalUnpairArithmeticProof.notLessWeak a b hl) hab)

theorem backward (a b m fuel : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum m a b)))
    (ha : Nonempty (Derivation body Delta (InternalLessThan.strictLess a (suc fuel))))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess b (suc fuel)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess m (suc fuel))) := by
  let L := InternalLessThan.strictLess a b
  apply formulaCases L
  · have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := valueUnique OriginalBoundsRecombination.maximum m b ![a,b] (withHyp hm L) (rightValue a b hl)
    exact InternalOriginalPairingOrderArithmeticProof.strictTransport m (suc fuel) b (suc fuel) he ⟨refl _⟩ (withHyp hb L)
  · have hl : Nonempty (Derivation body (L.not :: Delta) L.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have he := valueUnique OriginalBoundsRecombination.maximum m a ![a,b] (withHyp hm L.not) (leftValue a b hl)
    exact InternalOriginalPairingOrderArithmeticProof.strictTransport m (suc fuel) a (suc fuel) he ⟨refl _⟩ (withHyp ha L.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof

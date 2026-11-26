module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.CrossProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.RawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open NumericDependencyCross
variable {n : Nat}

theorem atChildren (source target out node a b left right : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)))
    (hv : Nonempty (Derivation body Delta (graph2 rawDependencies out source target)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b)))
    (hl : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children left source)))
    (hr : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children right target))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) a ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) b)) := by
  let xs : Fin 2 → OTerm alpha := ![source,target]
  let lp : Program 2 := .composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 0)
  let rp : Program 2 := .composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 1)
  have hlp : Nonempty (Derivation body Delta (programGraph lp left xs)) :=
    unaryValue ArgumentEntriesChildren.children (.projection 0) left source xs hl (projectionValue 0 xs)
  have hrp : Nonempty (Derivation body Delta (programGraph rp right xs)) :=
    unaryValue ArgumentEntriesChildren.children (.projection 1) right target xs hr (projectionValue 1 xs)
  have hc := binaryRecover cross lp rp out left right xs hv hlp hrp
  have hi := CrossProof.projection left right out node a b hc hm hq
  exact andIntro (ChildrenProof.childrenClosed n body alpha Delta source left a hs hl (andLeft hi))
    (ChildrenProof.childrenClosed n body alpha Delta target right b ht hr (andRight hi))

theorem atLeft (source target out node a b left : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)))
    (hv : Nonempty (Derivation body Delta (graph2 rawDependencies out source target)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b)))
    (hl : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children left source))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) a ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) b)) := by
  apply programCases ArgumentEntriesChildren.children (Fin.cons target Fin.elim0) _
  intro beta j Theta right hj hr
  simp only [conjunctionRename,graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hr
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hqj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact atChildren (source.relabel j) (target.relabel j) (out.relabel j) (node.relabel j)
    (a.relabel j) (b.relabel j) (left.relabel j) right hsj htj hvj hmj hqj hlj hr

theorem rawClosed (source target out node a b : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)))
    (hv : Nonempty (Derivation body Delta (graph2 rawDependencies out source target)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) a ⊓
      graph1 (OriginalCodeValidityGuard.check n) (numeral 1) b)) := by
  apply programCases ArgumentEntriesChildren.children (Fin.cons source Fin.elim0) _
  intro beta j Theta left hj hl
  simp only [conjunctionRename,graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hl
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hqj
  exact atLeft (source.relabel j) (target.relabel j) (out.relabel j) (node.relabel j)
    (a.relabel j) (b.relabel j) left hsj htj hvj hmj hqj hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.RawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.RawProof

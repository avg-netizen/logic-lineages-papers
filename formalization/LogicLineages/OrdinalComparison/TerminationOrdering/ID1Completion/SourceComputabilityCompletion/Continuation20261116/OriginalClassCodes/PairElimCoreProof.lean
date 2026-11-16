module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimCoreProof
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
open Continuation20261115
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open PairElimInductionDefinitions PairElimInductionSyntaxProof PairElimBindingProof

theorem atValues (raw head tail param out rest node a b mappedHead : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 pairRoots rest tail param)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mappedHead param head))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply formulaCases (eqn mappedHead node)
  · have hh' := outputTransport InternalPairing.pairing mappedHead node ![param,head]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hh _)
    have hmem := containsHit raw head tail head (withHyp hc (eqn mappedHead node)) (by rw [equalEqn]; exact ⟨refl head⟩)
    exact PairImageProof.introduce raw param node head hmem hh'
  · have hn : Nonempty (Derivation body ((eqn mappedHead node).not :: Delta) (equal mappedHead node).not) := by
      rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover out mappedHead rest node (numeral 1)
      (withHyp ho _) hn (withHyp hm _)
    have hi := belowRawApply raw tail param rest node a b (withHyp ih _)
      (consTailDescent raw head tail (withHyp hc _))
      (andIntro (withHyp hr _) ht)
    exact PairElimSupportProof.tailLift raw head tail param node (withHyp hc _) hi

theorem consCore (raw head tail param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph2 pairRoots out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
 :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  let qs : Fin 2 → Program 3 := ![.composition InternalPairing.pairing ![.projection 2,.projection 0],
    .composition pairRoots ![.projection 1,.projection 2]]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs ![head,tail,param] _
  intro beta j ys Theta hj hvals
  simp only [result,PairImageProof.imageRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  let xs : Fin 3 → OTerm beta := ![head.relabel j,tail.relabel j,param.relabel j]
  have hh := binaryRecover InternalPairing.pairing (.projection 2) (.projection 0)
    (ys 0) (param.relabel j) (head.relabel j) xs (hvals 0) (projectionValue 2 xs) (projectionValue 0 xs)
  have hr := binaryRecover pairRoots (.projection 1) (.projection 2)
    (ys 1) (tail.relabel j) (param.relabel j) xs (hvals 1) (projectionValue 1 xs) (projectionValue 2 xs)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have ho := PairRecursionProof.consForward (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (ys 0) (ys 1) (out.relabel j) hcj hh hr hvj
  exact atValues (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (ys 1) (node.relabel j) (a.relabel j) (b.relabel j) (ys 0) ihj hcj hr ho hmj hh

theorem core (raw param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hv : Nonempty (Derivation body Delta (graph2 pairRoots out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node))) :
    Nonempty (Derivation body Delta (result raw param out node a b)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · have hv0 := headTransport pairRoots out raw z ![param]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
    obtain ⟨hf⟩ := PairElimSupportProof.nilImpossible param out node hv0 (withHyp hm _)
    exact ⟨Derivation.explosion hf⟩
  · intro beta j Theta head tail hj hc
    simp only [result,PairImageProof.imageRename]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ihj
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hvj
    have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
    simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hmj
    exact consCore (raw.relabel j) head tail (param.relabel j) (out.relabel j)
      (node.relabel j) (a.relabel j) (b.relabel j) ihj hc hvj hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimCoreProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimCoreProof
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
open MapElimInductionDefinitions MapElimInductionSyntaxProof MapElimBindingProof
variable (F : Program 1)

theorem atValues (raw head tail param out rest node a b mappedHead : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) rest tail)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
    (hh : Nonempty (Derivation body Delta (graph1 F mappedHead head))) :
    Nonempty (Derivation body Delta (result F raw param out node a b)) := by
  apply formulaCases (eqn mappedHead node)
  · have hh' := outputTransport F mappedHead node ![head]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hh _)
    have hmem := containsHit raw head tail head (withHyp hc _) (by rw [equalEqn]; exact ⟨refl head⟩)
    exact MapImageProof.introduce F raw node head hmem hh'
  · have hn : Nonempty (Derivation body ((eqn mappedHead node).not :: Delta) (equal mappedHead node).not) := by
      rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover out mappedHead rest node (numeral 1)
      (withHyp ho _) hn (withHyp hm _)
    have hi := belowRawApply F raw tail param rest node a b (withHyp ih _)
      (consTailDescent raw head tail (withHyp hc _))
      (andIntro (withHyp hr _) ht)
    exact MapElimSupportProof.tailLift F raw head tail node (withHyp hc _) hi

theorem consCore (raw head tail param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) out raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node)))
 :
    Nonempty (Derivation body Delta (result F raw param out node a b)) := by
  let qs : Fin 2 → Program 2 := ![.composition F (fun _ : Fin 1 => .projection 0),
    .composition (InternalListMap.map F) (fun _ : Fin 1 => .projection 1) ]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons head (Fin.cons tail Fin.elim0)) _
  intro beta j ys Theta hj hvals
  simp only [result,MapImageProof.imageRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hvals
  let xs : Fin 2 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (tail.relabel j) Fin.elim0)
  have hh := unaryRecover F (.projection 0) (ys 0) (head.relabel j) xs (hvals 0) (projectionValue 0 xs)
  have hr := unaryRecover (InternalListMap.map F) (.projection 1) (ys 1) (tail.relabel j) xs (hvals 1) (projectionValue 1 xs)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have ho := InternalListMapProof.consForward F (raw.relabel j) (head.relabel j) (tail.relabel j)
    (ys 0) (ys 1) (out.relabel j) Fin.elim0 hcj hh hr hvj
  exact atValues F (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (ys 1) (node.relabel j) (a.relabel j) (b.relabel j) (ys 0) ihj hcj hr ho hmj hh

theorem core (raw param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) out raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node))) :
    Nonempty (Derivation body Delta (result F raw param out node a b)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · have hv0 := headTransport (InternalListMap.map F) out raw z Fin.elim0
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv _)
    obtain ⟨hf⟩ := MapElimSupportProof.nilImpossible F out node hv0 (withHyp hm _)
    exact ⟨Derivation.explosion hf⟩
  · intro beta j Theta head tail hj hc
    simp only [result,MapImageProof.imageRename]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ihj
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hvj
    have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
    simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hmj
    exact consCore F (raw.relabel j) head tail (param.relabel j) (out.relabel j)
      (node.relabel j) (a.relabel j) (b.relabel j) ihj hc hvj hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimCoreProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroCoreProof
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
open MapIntroInductionDefinitions MapIntroInductionSyntaxProof MapIntroBindingProof
variable (F : Program 1)

theorem atValues (raw head tail param out rest node a b mappedHead : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) rest tail)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph1 F node b)))
    (hh : Nonempty (Derivation body Delta (graph1 F mappedHead head))) :
    Nonempty (Derivation body Delta (result F raw param out node a b)) := by
  apply formulaCases (eqn head b)
  · have hh' := headTransport F mappedHead head b Fin.elim0
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hh _)
    have heq := valueUnique F mappedHead node ![b] hh' (withHyp hq _)
    exact containsHit out mappedHead rest node (withHyp ho _) (by rw [equalEqn]; exact heq)
  · have hn : Nonempty (Derivation body ((eqn head b).not :: Delta) (equal head b).not) := by
      rw [equalEqn]; exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := PrimaryMembership.Proof.missRecover raw head tail b (numeral 1)
      (withHyp hc _) hn (withHyp hm _)
    have hi := belowRawApply F raw tail param rest node a b (withHyp ih _)
      (consTailDescent raw head tail (withHyp hc _))
      (andIntro (andIntro (withHyp hr _) ht) (withHyp hq _))
    exact NumericDependencyCross.SupportProof.memberTail out mappedHead rest node (withHyp ho _) hi

theorem consCore (raw head tail param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) out raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph1 F node b))) :
    Nonempty (Derivation body Delta (result F raw param out node a b)) := by
  let qs : Fin 2 → Program 2 := ![.composition F ![.projection 0],
    .composition (InternalListMap.map F) ![.projection 1]]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons head (Fin.cons tail Fin.elim0)) _
  intro beta j ys Theta hj hvals
  simp only [result,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hvals
  let xs : Fin 2 → OTerm beta := ![head.relabel j,tail.relabel j]
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
  have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
  simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at hqj
  have ho := InternalListMapProof.consForward F (raw.relabel j) (head.relabel j) (tail.relabel j)
    (ys 0) (ys 1) (out.relabel j) Fin.elim0 hcj hh hr hvj
  exact atValues F (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (ys 1) (node.relabel j) (a.relabel j) (b.relabel j) (ys 0) ihj hcj hr ho hmj hqj hh

theorem core (raw param out node a b : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw F raw)))
    (hv : Nonempty (Derivation body Delta (graph1 (InternalListMap.map F) out raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw b)))
    (hq : Nonempty (Derivation body Delta (graph1 F node b))) :
    Nonempty (Derivation body Delta (result F raw param out node a b)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · have hm0 := headTransport contains (numeral 1) raw z (Fin.cons b Fin.elim0)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm _)
    obtain ⟨hn⟩ := valueUnique contains (numeral 1) z ![z,b] hm0 (containsNil b)
    exact ⟨Derivation.explosion (sucNeZeroApply hn)⟩
  · intro beta j Theta head tail hj hc
    simp only [result,conjunctionRename,eqnRelabel,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at ihj
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hvj
    have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hmj
    have hqj := InternalGraphCompositionFunctionalityProof.renameInto hq j Theta hj
    simp only [graph1Rename,graph2Rename,graph3Rename,eqnRelabel,conjunctionRename,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hqj
    exact consCore F (raw.relabel j) head tail (param.relabel j) (out.relabel j)
      (node.relabel j) (a.relabel j) (b.relabel j) ihj hc hvj hmj hqj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroCoreProof

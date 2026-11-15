module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.ConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SupportProof

theorem withRest (D : Program 2) (raw head tail param out child rest : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hr : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) rest tail param)))
    (hs : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.flattenStep D) out head rest param)))
    : Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  apply programCases D (Fin.cons head (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hd
  rw [predecessorRename]
  simp only [consTermRename,emptyRename] at hd
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hmj := renameInto hm j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hrj := renameInto hr j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hsj := renameInto hs j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  exact atDeps D (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (child.relabel j) (rest.relabel j) deps hbj hcj hmj hrj hsj hd

theorem consCore (D : Program 2) (raw head tail param out child : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hf : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out raw param)))
    : Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  have hstep := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 1)
    (ExchangeFrontier.flattenStep D) raw head tail out (Fin.cons param Fin.elim0) hc hf
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 1)
    (ExchangeFrontier.flattenStep D) out head tail (Fin.cons param Fin.elim0) _ hstep
  intro beta j Theta rest hj hr hs
  rw [predecessorRename]
  have hparams : (fun i => ((Fin.cons param Fin.elim0 : Fin 1 → OTerm alpha) i).relabel j) =
      Fin.cons (param.relabel j) Fin.elim0 := by
    funext i
    exact Fin.cases rfl (fun k => Fin.elim0 k) i
  rw [hparams] at hr hs
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hmj := renameInto hm j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfj := renameInto hf j Theta hj
  simp only [belowRawRename,graph1Rename,graph2Rename,graph3Rename,eqnRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  exact withRest D (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (out.relabel j) (child.relabel j) rest hbj hcj hmj hr hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.ConsProof

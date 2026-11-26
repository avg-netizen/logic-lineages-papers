module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalMixedDirectBottomTraceInductionDefinitions OriginalHereditaryLambdaChildStateProof
/-- Proof-side branch interface, discharged by actual branch proofs at final specialization. -/
def BranchStep (body : Positive (Fin 1)) (source : Program 2) (leaf guard child : Program 4) : Prop :=
 ∀ (beta : Type) (Theta : List (Formula beta))
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out : OTerm beta),
 Nonempty (Derivation body Theta (BelowPath source leaf path)) →
 Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode path head tail)) →
 Nonempty (Derivation body Theta (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)) →
 Nonempty (Derivation body Theta (graph4 guard (suc z) s t cert oldParam)) →
 Nonempty (Derivation body Theta (graph4 child next s t cert oldParam)) →
 Nonempty (Derivation body Theta (InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)) →
 Nonempty (Derivation body Theta (graph1 (finish source leaf) (suc z) out)) →
 Nonempty (Derivation body Theta (result source leaf s t newParam erasedS erasedT))

theorem atSelected (source : Program 2) (leaf guard child : Program 4)
 (step : BranchStep body source leaf guard child)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT state next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert oldParam)))
 (hb : Nonempty (Derivation body Delta
  (graph1 (OriginalHereditaryLambda.atState (InternalAcceptance.conjunction guard leaf)) (suc z) state ⊓
   graph1 (OriginalHereditaryLambda.atState child) next state)))
 (hr : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)))
 (hz : Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out))) :
 Nonempty (Derivation body Delta (result source leaf s t newParam erasedS erasedT)) := by
 have hhop := atLiveRecover (InternalAcceptance.conjunction guard leaf) (suc z) state s t cert oldParam hl (andLeft hb)
 have hg := conjunctionRecover guard leaf ![s,t,cert,oldParam] hhop
 have hchild := atLiveRecover child next state s t cert oldParam hl (andRight hb)
 exact step alpha Delta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out
  hi hc hf (andLeft hg) hchild hr hz

theorem atConsGeneric (source : Program 2) (leaf : Program 4)
 (lambdaStep : BranchStep body source leaf (OriginalTransparentLambdaStep.hopGuard source) OriginalHereditaryLambda.childLive)
 (appStep : BranchStep body source leaf (OriginalTransparentApplicationFunctionDefinitions.hopGuard source) OriginalTransparentApplicationFunctionDefinitions.childLive)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT))) :
 Nonempty (Derivation body Delta (result source leaf s t newParam erasedS erasedT)) := by
 apply OriginalMixedDirectBottomTraceFrontQueryProof.frontCases source leaf s t cert oldParam path head tail _
  (andLeft hf) hc (andLeft (andRight (andRight (andRight hf))))
 intro beta j Theta state next out incl hl hb hr hz
 rw [OriginalMixedDirectBottomTraceInductionSyntaxProof.resultRename]
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 rw [OriginalMixedDirectBottomTraceInductionSyntaxProof.belowPathRename] at hi'
 rw [OriginalMixedDirectBottomTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [graph2Rename] at hc'
 let A := graph1 (OriginalHereditaryLambda.atState (lambdaHop source leaf)) (suc z) state ⊓
  graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state
 let B := graph1 (OriginalHereditaryLambda.atState (applicationHop source leaf)) (suc z) state ⊓
  graph1 (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive) next state
 have go (guard child : Program 4) (step : BranchStep body source leaf guard child)
   (P : Formula beta)
   (h : Nonempty (Derivation body (P :: Theta)
    (graph1 (OriginalHereditaryLambda.atState (InternalAcceptance.conjunction guard leaf)) (suc z) state ⊓
     graph1 (OriginalHereditaryLambda.atState child) next state))) :=
  atSelected source leaf guard child step
   (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j)
   (cert.relabel j) (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
   (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j) state next out
   (withHyp hi' P) (withHyp hc' P) (withHyp hf' P) (withHyp hl P) h (withHyp hr P) (withHyp hz P)
 obtain ⟨ha⟩ := go _ _ lambdaStep A ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hb'⟩ := go _ _ appStep B ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hb⟩ := hb
 exact ⟨InternalBetaTotalityProof.disjunctionElimination hb (Derivation.implicationIntroduction ha) (Derivation.implicationIntroduction hb')⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceConsProof

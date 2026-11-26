module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCommonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EvaluatorConstructorInductionDefinitions EvaluatorConstructorFieldsSyntaxProof
open EvaluatorConstructorCongruenceDefinitions EvaluatorErasureDefinitions
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
theorem fromTransfer (Q R : Program 2) (H G : Program 1) (M W : Program 2)
 (transfer : ∀ (beta : Type) (Theta : List (Formula beta)) (left right parameter value : OTerm beta),
  Nonempty (Derivation body Theta (AdmittedPair R H G M W left right parameter)) →
  Nonempty (Derivation body Theta (graph2 Q value left parameter)) →
  Nonempty (Derivation body Theta (graph2 Q value right parameter)))
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) (out other : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (applicationFields R H G M W count xs)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) out (xs 0) (xs 13))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) other (xs 1) (xs 13)))) :
 Nonempty (Derivation body Delta (equal out other)) := by
 let qf : Program 3 := .composition Q ![.projection 0,.projection 2]
 let qa : Program 3 := .composition Q ![.projection 1,.projection 2]
 apply programsCases (![qf,qa] : Fin 2 → Program 3)
  (Fin.cons (xs 2) (Fin.cons (xs 4) (Fin.cons (xs 13) Fin.elim0))) _
 intro beta j Theta ys hj hq
 rw [equalRename]
 simp only [consTermRename,emptyRename] at hq
 let args : Fin 3 → OTerm beta := Fin.cons ((xs 2).relabel j)
  (Fin.cons ((xs 4).relabel j) (Fin.cons ((xs 13).relabel j) Fin.elim0))
 have hvf := binaryRecover Q (.projection 0) (.projection 2) (ys 0)
  ((xs 2).relabel j) ((xs 13).relabel j) args (hq 0) (projectionValue 0 args) (projectionValue 2 args)
 have hva := binaryRecover Q (.projection 1) (.projection 2) (ys 1)
  ((xs 4).relabel j) ((xs 13).relabel j) args (hq 1) (projectionValue 1 args) (projectionValue 2 args)
 have hf' := renameInto hf j Theta hj
 rw [applicationRename] at hf'
 have ho' := renameInto ho j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [graph2Rename] at ho' hr'
 have pf := andLeft (andRight (andRight (andRight (andRight hf'))))
 have pa := andLeft (andRight (andRight (andRight (andRight (andRight hf')))))
 have hvf' := transfer beta Theta ((xs 2).relabel j) ((xs 3).relabel j) ((xs 13).relabel j) (ys 0) pf hvf
 have hva' := transfer beta Theta ((xs 4).relabel j) ((xs 5).relabel j) ((xs 13).relabel j) (ys 1) pa hva
 exact EvaluatorConstructorApplicationRootCommonProof.sameChildValues Q R H G M W (count.relabel j)
  (fun i => (xs i).relabel j) (ys 0) (ys 1) (out.relabel j) (other.relabel j)
  hf' hvf hvf' hva hva' ho' hr'

theorem retainedRoot (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) (out other : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (applicationFields R H G M W count xs)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out (xs 0) (xs 13))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) other (xs 1) (xs 13)))) :
 Nonempty (Derivation body Delta (equal out other)) :=
 fromTransfer R R H G M W (compat body) count xs out other hf ho hr

theorem evaluatorRoot (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) (out other : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (applicationFields R H G M W count xs)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) out (xs 0) (xs 13))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) other (xs 1) (xs 13)))) :
 Nonempty (Derivation body Delta (equal out other)) := by
 apply fromTransfer (OriginalHereditaryEvaluatorDefinitions.evaluator R) R H G M W _ count xs out other hf ho hr
 intro beta Theta left right parameter value pair hv
 exact EvaluatorConstructorValueProof.evaluatorValue R left right parameter value (andRight (andRight pair)) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootTransferProof

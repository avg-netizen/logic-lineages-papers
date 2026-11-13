module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorConstructorInductionDefinitions EvaluatorConstructorFieldsSyntaxProof
open EvaluatorConstructorCongruenceDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem retainedRoot (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha) (out other : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (lambdaFields R H G M W count xs)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out (xs 0) (xs 6))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) other (xs 1) (xs 6)))) :
 Nonempty (Derivation body Delta (equal out other)) := by
 apply programCases R (Fin.cons (xs 2) (Fin.cons (xs 7) Fin.elim0)) _
 intro beta j Theta value hj hv
 rw [equalRename]
 simp only [consTermRename,emptyRename] at hv
 have hf' := renameInto hf j Theta hj
 rw [lambdaRename] at hf'
 have ho' := renameInto ho j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph2Rename] at ho' hr'
 have h2 := andLeft (andRight (andRight hf'))
 have h3 := andLeft (andRight (andRight (andRight hf')))
 have h4 := andLeft (andRight (andRight (andRight (andRight hf'))))
 have h5 := andLeft (andRight (andRight (andRight (andRight (andRight hf')))))
 have h6 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))
 have h7 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))
 have h8 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))))
 have h9 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))))
 have hv' := compat body beta Theta ((xs 2).relabel j) ((xs 3).relabel j) ((xs 7).relabel j) value h9 hv
 exact EvaluatorConstructorLambdaRootProof.sameChildValue R
   ((xs 0).relabel j) ((xs 1).relabel j) ((xs 4).relabel j) ((xs 5).relabel j)
   ((xs 2).relabel j) ((xs 3).relabel j) ((xs 6).relabel j) ((xs 7).relabel j)
   ((xs 8).relabel j) ((xs 9).relabel j) ((xs 10).relabel j) value
   (out.relabel j) (other.relabel j) h7 h8 h5 h6 h2 h3 h4 hv hv' ho' hr'
theorem evaluatorRoot (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha) (out other : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (lambdaFields R H G M W count xs)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) out (xs 0) (xs 6))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) other (xs 1) (xs 6)))) :
 Nonempty (Derivation body Delta (equal out other)) := by
 apply programCases (OriginalHereditaryEvaluatorDefinitions.evaluator R) (Fin.cons (xs 2) (Fin.cons (xs 7) Fin.elim0)) _
 intro beta j Theta value hj hv
 rw [equalRename]
 simp only [consTermRename,emptyRename] at hv
 have hf' := renameInto hf j Theta hj
 rw [lambdaRename] at hf'
 have ho' := renameInto ho j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph2Rename] at ho' hr'
 have h2 := andLeft (andRight (andRight hf'))
 have h3 := andLeft (andRight (andRight (andRight hf')))
 have h4 := andLeft (andRight (andRight (andRight (andRight hf'))))
 have h5 := andLeft (andRight (andRight (andRight (andRight (andRight hf')))))
 have h6 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))
 have h7 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))
 have h8 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf'))))))))
 have h9 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf')))))))))
 have hv' := EvaluatorConstructorValueProof.evaluatorValue R ((xs 2).relabel j) ((xs 3).relabel j) ((xs 7).relabel j) value (andRight (andRight h9)) hv
 exact EvaluatorConstructorLambdaRootProof.sameChildValue (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   ((xs 0).relabel j) ((xs 1).relabel j) ((xs 4).relabel j) ((xs 5).relabel j)
   ((xs 2).relabel j) ((xs 3).relabel j) ((xs 6).relabel j) ((xs 7).relabel j)
   ((xs 8).relabel j) ((xs 9).relabel j) ((xs 10).relabel j) value
   (out.relabel j) (other.relabel j) h7 h8 h5 h6 h2 h3 h4 hv hv' ho' hr'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootTransferProof

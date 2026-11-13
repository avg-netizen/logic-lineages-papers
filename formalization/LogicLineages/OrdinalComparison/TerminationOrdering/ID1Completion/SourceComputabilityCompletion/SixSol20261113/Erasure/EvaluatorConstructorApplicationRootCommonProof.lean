module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootAtCodesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCodeQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorFieldsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCommonProof
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
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
theorem sameChildValues (Q R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) (fv av out other : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (applicationFields R H G M W count xs)))
 (hfL : Nonempty (Derivation body Delta (graph2 Q fv (xs 2) (xs 13))))
 (hfR : Nonempty (Derivation body Delta (graph2 Q fv (xs 3) (xs 13))))
 (haL : Nonempty (Derivation body Delta (graph2 Q av (xs 4) (xs 13))))
 (haR : Nonempty (Derivation body Delta (graph2 Q av (xs 5) (xs 13))))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) out (xs 0) (xs 13))))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) other (xs 1) (xs 13)))) :
 Nonempty (Derivation body Delta (equal out other)) := by
 apply EvaluatorConstructorApplicationRootCodeQueries.actualCases (xs 7) (xs 8) (xs 6) fv av _
 intro beta j Theta fo ao obs td data candidate hj hfo hao hobs htd hdata hcan
 rw [equalRename]
 have hs' := renameInto hs j Theta hj
 rw [applicationRename] at hs'
 have hfL' := renameInto hfL j Theta hj
 have hfR' := renameInto hfR j Theta hj
 have haL' := renameInto haL j Theta hj
 have haR' := renameInto haR j Theta hj
 have ho' := renameInto ho j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [graph2Rename] at hfL' hfR' haL' haR' ho' hr'
 have cl := EvaluatorConstructorApplicationRootAtCodesProof.actualRoot Q
  ((xs 6).relabel j) ((xs 7).relabel j) ((xs 8).relabel j) ((xs 9).relabel j) ((xs 11).relabel j)
  ((xs 2).relabel j) ((xs 4).relabel j) ((xs 0).relabel j) ((xs 13).relabel j)
  (fv.relabel j) (av.relabel j) fo ao obs td data candidate
  (andLeft (andRight (andRight hs'))) hfL' haL' hfo hao hobs htd hdata hcan
 have cr := EvaluatorConstructorApplicationRootAtCodesProof.actualRoot Q
  ((xs 6).relabel j) ((xs 7).relabel j) ((xs 8).relabel j) ((xs 10).relabel j) ((xs 12).relabel j)
  ((xs 3).relabel j) ((xs 5).relabel j) ((xs 1).relabel j) ((xs 13).relabel j)
  (fv.relabel j) (av.relabel j) fo ao obs td data candidate
  (andLeft (andRight (andRight (andRight hs')))) hfR' haR' hfo hao hobs htd hdata hcan
 obtain ⟨eqL⟩ := valueUnique (OriginalRootObservation.rootObservation Q) (out.relabel j) candidate
  (Fin.cons ((xs 0).relabel j) (Fin.cons ((xs 13).relabel j) Fin.elim0)) ho' cl
 obtain ⟨eqR⟩ := valueUnique (OriginalRootObservation.rootObservation Q) candidate (other.relabel j)
  (Fin.cons ((xs 1).relabel j) (Fin.cons ((xs 13).relabel j) Fin.elim0)) cr hr'
 rw [equalEqn]
 exact ⟨InternalTagArithmeticSupportProof.trans eqL eqR⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCommonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationRootCommonProof

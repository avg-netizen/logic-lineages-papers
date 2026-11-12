module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionEmptyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnRelabel sucRelabel)
open OriginalTypedDecoderInternalAcceptanceUnaryProof (notRename)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalNumericIterationProof (frontSuccForward)
open InternalSquareRootArithmeticSupportProof (strictWeakTrans)
open OriginalHereditaryPotentialCompletion OriginalHereditaryPotentialCompletionSyntaxProof
open OriginalHereditaryPotentialCompletionEmptyProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rowApply (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel input work results before output : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (Row R H M W c B fuel)))
 (he : Nonempty (Derivation body Delta (Entry R H M W c B fuel input work results before output))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) := by
 have h := actualFiniteUniversalElimination body alpha 5 Delta (rowBody R H M W c B fuel)
  (fun i => emb (![input,work,results,before,output] i)) hrow
 rw [bodyWitness] at h
 exact ⟨Derivation.implicationElimination (Classical.choice h) (Classical.choice he)⟩
theorem zeroCore (R : Program 2) (H : Program 1) (M W : Program 2) (supply : StepLaw R H M W)
 (c B input work results before output : OTerm alpha)
 (he : Nonempty (Derivation body Delta (Entry R H M W c B z input work results before output))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) := by
 apply formulaCases (eqn work z) _
 · have hz : Nonempty (Derivation body (eqn work z :: Delta) (eqn work z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he' := withHyp he (eqn work z)
   exact emptyRun R z input output (fromWorkZero input work results (andLeft he') hz)
    (andRight (andRight (andRight (andRight he'))))
 · let A := (eqn work z).not
   have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he' := withHyp he A
   apply OriginalHereditaryPotentialCompletionQueryProof.stepCases R input B _
   intro beta j Theta next nw nr after hj hs hp hm
   rw [emptyRename]
   have he'' := renameInto he' j Theta hj
   have hn' := renameInto hn j Theta hj
   simp only [A,entryRename,InternalTagArithmeticSyntaxProof.zRelabel,notRename,eqnRelabel] at he'' hn'
   have hd := supply body beta Theta (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j)
     (results.relabel j) (before.relabel j) next nw nr after
     (andLeft he'') (andLeft (andRight he'')) (andLeft (andRight (andRight he''))) hn' hs hp hm
   have hz := strictWeakTrans after (before.relabel j) z (andRight hd) (andLeft (andRight (andRight (andRight he''))))
   have hnz := InternalBoundedDescentNormalizerStepProof.notLessZero (body:=body) (Gamma:=Theta) after
   exact ⟨Derivation.explosion (Derivation.implicationElimination (Classical.choice hnz) (Classical.choice hz))⟩
theorem successorCore (R : Program 2) (H : Program 1) (M W : Program 2) (supply : StepLaw R H M W)
 (c B fuel input work results before output : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (Row R H M W c B fuel)))
 (he : Nonempty (Derivation body Delta (Entry R H M W c B (suc fuel) input work results before output))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) := by
 apply formulaCases (eqn work z) _
 · have hz : Nonempty (Derivation body (eqn work z :: Delta) (eqn work z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he' := withHyp he (eqn work z)
   exact emptyRun R (suc fuel) input output (fromWorkZero input work results (andLeft he') hz)
    (andRight (andRight (andRight (andRight he'))))
 · let A := (eqn work z).not
   have hn : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he' := withHyp he A
   have hrow' := withHyp hrow A
   apply OriginalHereditaryPotentialCompletionQueryProof.stepCases R input B _
   intro beta j Theta next nw nr after hj hs hp hm
   rw [emptyRename]
   have he'' := renameInto he' j Theta hj
   have hn' := renameInto hn j Theta hj
   have hrow'' := renameInto hrow' j Theta hj
   simp only [A,entryRename,rowRename,sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel,notRename,eqnRelabel] at he'' hn' hrow''
   have hd := supply body beta Theta (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j)
     (results.relabel j) (before.relabel j) next nw nr after
     (andLeft he'') (andLeft (andRight he'')) (andLeft (andRight (andRight he''))) hn' hs hp hm
   have hb := strictWeakTrans after (before.relabel j) (suc (fuel.relabel j)) (andRight hd) (andLeft (andRight (andRight (andRight he''))))
   have ht := frontSuccForward (OriginalHereditaryCombinedStep.step R) (fuel.relabel j) (output.relabel j) (input.relabel j) next hs
     (andRight (andRight (andRight (andRight he''))))
   exact rowApply R H M W (c.relabel j) (B.relabel j) (fuel.relabel j) next nw nr after (output.relabel j)
     hrow'' (andIntro hp (andIntro (andLeft hd) (andIntro hm (andIntro hb ht))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionCoreProof

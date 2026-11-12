module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaOpenedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphCompositionFunctionalityProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalPositionStructuralKeyOpeningDefinitions OriginalClassContextAllPositionObserver
open UniformCertificateCompletion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalTagArithmeticSyntaxProof (suc sucRelabel)
theorem direction (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out d e child childOut parameter childParameter cutoff childMark mark : OTerm alpha)
 (hrange : Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)))
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)))
 (hsc : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) child childParameter)))
 (hsco : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) childOut childParameter)))
 (hfi : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input d e child parameter childParameter)))
 (hfo : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields out d e childOut parameter childParameter)))
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (hout : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hoc : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) childMark (suc cutoff) child childParameter)))
 (hoco : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) childMark (suc cutoff) childOut childParameter)))
 (hmark : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff out parameter))) :
 Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff input parameter)) := by
 have hwout := BottomDescentStepProof.windowChange p.window InternalOriginalStepGuard.one input out parameter hw
 apply OriginalPositionStructuralKeyOpeningProof.actualOpening p H G W body alpha Delta
   out parameter cutoff mark _ ho hwout hrange hmark
 intro beta j Theta context gamma erasedType deleted outE erasedParam keyValue rank hj opened
 rw [graph3Rename]
 have hw := renameInto hw j Theta hj
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,graph2Rename,InternalOriginalStepGuard.one,sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hw
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hs
 have ho := renameInto ho j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at ho
 have hsc := renameInto hsc j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hsc
 have hsco := renameInto hsco j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hsco
 have hfi := renameInto hfi j Theta hj
 simp only [OriginalLambdaTraversalInternalFieldsSyntaxProof.lambdaFieldsRename] at hfi
 have hfo := renameInto hfo j Theta hj
 simp only [OriginalLambdaTraversalInternalFieldsSyntaxProof.lambdaFieldsRename] at hfo
 have hi := renameInto hi j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hi
 have hout := renameInto hout j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hout
 have hoc := renameInto hoc j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hoc
 have hoco := renameInto hoco j Theta hj
 simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,sucRelabel] at hoco
 exact OriginalPositionStructuralKeyLambdaOpenedProof.atOpened p H G W
   (input.relabel j) (out.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (childOut.relabel j) (parameter.relabel j) (childParameter.relabel j) (cutoff.relabel j) (childMark.relabel j) (mark.relabel j) context gamma erasedType deleted outE erasedParam keyValue rank
   hw hs ho hsc hsco hfi hfo hi hout hoc hoco opened

theorem actualLambda : OriginalPositionStructuralKeyLambdaTargets.ActualLambda := by
 intro p H G W body alpha Delta input out d e child childOut parameter childParameter cutoff childMark mark
 dsimp only
 intro hrange hw hs ho hsc hsco hfi hfo hi hout hoc hoco
 let O := positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)
 let A := graph3 O mark cutoff out parameter
 let B := graph3 O mark cutoff input parameter
 have hwout := BottomDescentStepProof.windowChange p.window InternalOriginalStepGuard.one input out parameter hw
 have forward : Nonempty (Derivation body (A :: Delta) B) := by
   exact direction p H G W input out d e child childOut parameter childParameter cutoff childMark mark
     (withHyp hrange A) (withHyp hw A) (withHyp hs A) (withHyp ho A)
     (withHyp hsc A) (withHyp hsco A) (withHyp hfi A) (withHyp hfo A)
     (withHyp hi A) (withHyp hout A) (withHyp hoc A) (withHyp hoco A)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 have backward : Nonempty (Derivation body (B :: Delta) A) := by
   exact direction p H G W out input d e childOut child parameter childParameter cutoff childMark mark
     (withHyp hrange B) (withHyp hwout B) (withHyp ho B) (withHyp hs B)
     (withHyp hsco B) (withHyp hsc B) (withHyp hfo B) (withHyp hfi B)
     (withHyp hout B) (withHyp hi B) (withHyp hoco B) (withHyp hoc B)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hf⟩ := forward
 obtain ⟨hb⟩ := backward
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaProof

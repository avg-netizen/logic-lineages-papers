module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationOpenedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationProof
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

theorem direction (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out domain codomain arrow fn arg fnOut argOut parameter cutoff fMark aMark mark : OTerm alpha)
 (hrange : Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)))
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window input parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) out parameter)))
 (hsf : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) fn parameter)))
 (hsa : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) arg parameter)))
 (hsfo : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) fnOut parameter)))
 (hsao : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) argOut parameter)))
 (harr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain codomain)))
 (htf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)))
 (htfo : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fnOut)))
 (hta : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain arg)))
 (htao : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain argOut)))
 (hi : Nonempty (Derivation body Delta (graph4 application input domain codomain fn arg)))
 (happout : Nonempty (Derivation body Delta (graph4 application out domain codomain fnOut argOut)))
 (hof : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) fMark cutoff fn parameter)))
 (hofo : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) fMark cutoff fnOut parameter)))
 (hoa : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) aMark cutoff arg parameter)))
 (hoao : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) aMark cutoff argOut parameter)))
 (hmark : Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff out parameter))) :
 Nonempty (Derivation body Delta (graph3 (positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)) mark cutoff input parameter)) := by
 have hwout := BottomDescentStepProof.windowChange p.window InternalOriginalStepGuard.one input out parameter hw
 apply OriginalPositionStructuralKeyOpeningProof.actualOpening p H G W body alpha Delta
   out parameter cutoff mark _ ho hwout hrange hmark
 intro beta j Theta context gamma erasedType deleted outE erasedParam keyValue rank hj opened
 rw [graph3Rename]
 have hw := renameInto hw j Theta hj
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,graph2Rename,InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hw
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs
 have ho := renameInto ho j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at ho
 have hsf := renameInto hsf j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsf
 have hsa := renameInto hsa j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsa
 have hsfo := renameInto hsfo j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsfo
 have hsao := renameInto hsao j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsao
 have harr := renameInto harr j Theta hj
 simp only [graph2Rename] at harr
 have htf := renameInto htf j Theta hj
 simp only [graph1Rename] at htf
 have htfo := renameInto htfo j Theta hj
 simp only [graph1Rename] at htfo
 have hta := renameInto hta j Theta hj
 simp only [graph1Rename] at hta
 have htao := renameInto htao j Theta hj
 simp only [graph1Rename] at htao
 have hi := renameInto hi j Theta hj
 simp only [graph4Rename] at hi
 have happout := renameInto happout j Theta hj
 simp only [graph4Rename] at happout
 have hof := renameInto hof j Theta hj
 simp only [graph3Rename] at hof
 have hofo := renameInto hofo j Theta hj
 simp only [graph3Rename] at hofo
 have hoa := renameInto hoa j Theta hj
 simp only [graph3Rename] at hoa
 have hoao := renameInto hoao j Theta hj
 simp only [graph3Rename] at hoao
 let input := input.relabel j
 let out := out.relabel j
 let domain := domain.relabel j
 let codomain := codomain.relabel j
 let arrow := arrow.relabel j
 let fn := fn.relabel j
 let arg := arg.relabel j
 let fnOut := fnOut.relabel j
 let argOut := argOut.relabel j
 let parameter := parameter.relabel j
 let cutoff := cutoff.relabel j
 let fMark := fMark.relabel j
 let aMark := aMark.relabel j
 let mark := mark.relabel j
 exact OriginalPositionStructuralKeyApplicationOpenedProof.atOpened p H G W
   input out domain codomain arrow fn arg fnOut argOut parameter cutoff fMark aMark mark context gamma erasedType deleted outE erasedParam keyValue rank
   hw hs ho hsf hsa hsfo hsao harr htf htfo hta htao hi happout hof hofo hoa hoao opened

theorem actualApplication : OriginalPositionStructuralKeyApplicationTargets.ActualApplication := by
 intro p H G W body alpha Delta input out domain codomain arrow fn arg fnOut argOut parameter cutoff fMark aMark mark
 dsimp only
 intro hrange hw hs ho hsf hsa hsfo hsao harr htf htfo hta htao hi happout hof hofo hoa hoao
 let O := positionObservation (OriginalStructuralClassKeyDefinitions.key p H G W)
 let A := graph3 O mark cutoff out parameter
 let B := graph3 O mark cutoff input parameter
 have hwout := BottomDescentStepProof.windowChange p.window InternalOriginalStepGuard.one input out parameter hw
 have forward : Nonempty (Derivation body (A :: Delta) B) :=
   direction p H G W input out domain codomain arrow fn arg fnOut argOut parameter cutoff fMark aMark mark
     (withHyp hrange A)
     (withHyp hw A)
     (withHyp hs A)
     (withHyp ho A)
     (withHyp hsf A)
     (withHyp hsa A)
     (withHyp hsfo A)
     (withHyp hsao A)
     (withHyp harr A)
     (withHyp htf A)
     (withHyp htfo A)
     (withHyp hta A)
     (withHyp htao A)
     (withHyp hi A)
     (withHyp happout A)
     (withHyp hof A)
     (withHyp hofo A)
     (withHyp hoa A)
     (withHyp hoao A)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 have backward : Nonempty (Derivation body (B :: Delta) A) :=
   direction p H G W out input domain codomain arrow fnOut argOut fn arg parameter cutoff fMark aMark mark
     (withHyp hrange B)
     (withHyp hwout B)
     (withHyp ho B)
     (withHyp hs B)
     (withHyp hsfo B)
     (withHyp hsao B)
     (withHyp hsf B)
     (withHyp hsa B)
     (withHyp harr B)
     (withHyp htfo B)
     (withHyp htf B)
     (withHyp htao B)
     (withHyp hta B)
     (withHyp happout B)
     (withHyp hi B)
     (withHyp hofo B)
     (withHyp hof B)
     (withHyp hoao B)
     (withHyp hoa B)
     ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hf⟩ := forward
 obtain ⟨hb⟩ := backward
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.RootSoundnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalParameterizedApplicationStepChecker
open InternalParameterizedApplicationStepCheckerGraphProof (edgeStateValue)
open InternalParameterizedApplicationStepCheckerSyntaxProof (appendParameterThree)
open InternalParameterizedApplicationResultStack (liftP)
open InternalParameterizedApplicationResultStackWiringProof (wireValue)
open ScannerFieldsProof
open OriginalMixedDirectBottomTrace (recognizes)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Root soundness is applied to the actual normalized state's three
selectors, with its SAME separate parameter. No leaf invariant is assumed. -/
theorem selectedAtRecognizedState (S : Program 2) (leaf : Program 4)
 (state parameter : OTerm alpha)
 (ha : Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) state parameter))) :
 Nonempty (Derivation body Delta (graph2 (selectedCheckerP leaf) (suc z) state parameter)) := by
 apply edgeCases state _
 intro beta rho Theta s t cert hrho he
 simp only [graph2Rename,sucRelabel,zRelabel]
 have ha' := renameInto ha rho Theta hrho
 simp only [graph2Rename,sucRelabel,zRelabel] at ha'
 have hrec := wireRecoverAccepted S leaf (state.relabel rho) s t cert (parameter.relabel rho) he ha'
 have hleaf := andRight (RootSoundnessProof.recognizerRootSoundness S leaf
  body beta Theta s t cert (parameter.relabel rho) hrec)
 exact wireValue leaf ![source,target,step] (suc z) (state.relabel rho)
  (parameter.relabel rho) (Fin.cons s (Fin.cons t (Fin.cons cert Fin.elim0)))
  (by simpa only [appendParameterThree,graph4,SourceComputabilityFormulaSupportProof.numeral] using hleaf) (SelectedNilProof.selectorsAt s t cert (state.relabel rho) he)

theorem atKnownState (S : Program 2) (leaf : Program 4) (endpoint : Program 6)
 (s t cert parameter state : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes S leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (checkerP endpoint leaf) (suc z) s t cert parameter)) := by
 have hstep : ScannerRepeatProof.StepPreserves body (transitionP endpoint)
  (ScannerTargets.stateRecognizes S leaf) := by
  intro beta Theta initial next runtime ht hp
  exact ScannerStepProof.scannerPreservesRecognition S leaf endpoint body beta Theta
   initial next runtime ht hp
 have hstate := wireAccepted S leaf state s t cert parameter he ha
 let qs : Fin 2 → Program 2 := ![liftP InternalApplicationStepPeel.rawPath,normalizerP endpoint]
 let xs : Fin 2 → OTerm alpha := ![state,parameter]
 apply queryCases qs xs _
 intro beta rho ys Theta hrho hq
 simp only [graph4Rename,sucRelabel,zRelabel]
 have hx : (fun i => (xs i).relabel rho) = ![state.relabel rho,parameter.relabel rho] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
 have hh (i : Fin 2) : Nonempty (Derivation body Theta
  (programGraph (qs i) (ys i) ![state.relabel rho,parameter.relabel rho])) := by
  simpa only [hx] using hq i
 have he' := renameInto he rho Theta hrho
 simp only [graph3Rename] at he'
 have hstate' := renameInto hstate rho Theta hrho
 simp only [graph2Rename,sucRelabel,zRelabel] at hstate'
 let xx : Fin 2 → OTerm beta := ![state.relabel rho,parameter.relabel rho]
 have hr := compositionRecover (repeatP (transitionP endpoint))
  ![liftP InternalApplicationStepPeel.rawPath,.projection 0,.projection 1]
  (ys 1) xx ![ys 0,state.relabel rho,parameter.relabel rho] (hh 1)
  (by intro i; exact Fin.cases (hh 0) (Fin.cases (projectionValue 0 xx)
   (Fin.cases (projectionValue 1 xx) (fun j => Fin.elim0 j))) i)
 have hnormalized := ScannerRepeatProof.preserves (transitionP endpoint)
  (ScannerTargets.stateRecognizes S leaf) hstep
  (ys 0) (state.relabel rho) (ys 1) (parameter.relabel rho) hr hstate'
 have hselected := selectedAtRecognizedState S leaf (ys 1) (parameter.relabel rho) hnormalized
 have hchecked := binaryValue (selectedCheckerP leaf) (normalizerP endpoint) (.projection 1)
  (suc z) (ys 1) (parameter.relabel rho) xx hselected (hh 1) (projectionValue 1 xx)
 let root : Fin 4 → OTerm beta := ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho]
 exact binaryValue (checkedStateP endpoint leaf) edgeStateP (.projection 3)
  (suc z) (state.relabel rho) (parameter.relabel rho) root hchecked
  (edgeStateValue (state.relabel rho) (s.relabel rho) (t.relabel rho)
   (cert.relabel rho) (parameter.relabel rho) he') (projectionValue 3 root)

/-- Every step and every list-induction supplier is concretely discharged.
The selected checker uses its ORIGINAL endpoint, scanner, original path,
actual normalized state and unchanged original runtime parameter. -/
theorem recognizedSelectedChecker : ScannerTargets.RecognizedSelectedChecker := by
 intro S leaf endpoint body alpha Delta s t cert parameter ha
 apply programCases edgeCode (Fin.cons s (Fin.cons t (Fin.cons cert Fin.elim0))) _
 intro beta rho Theta state hrho he
 simp only [graph4Rename,sucRelabel,zRelabel]
 simp only [consTermRename,emptyRename] at he
 have ha' := renameInto ha rho Theta hrho
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 exact atKnownState S leaf endpoint (s.relabel rho) (t.relabel rho) (cert.relabel rho)
  (parameter.relabel rho) state he ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerProof

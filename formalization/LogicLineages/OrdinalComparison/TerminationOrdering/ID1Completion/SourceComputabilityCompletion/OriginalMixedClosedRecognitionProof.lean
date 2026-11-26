module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace

/-- Query the actual original path, live state and run output once, transfer
that accepting run, and reassemble recognition at the identical four inputs. -/
theorem recognizesFactor : OriginalMixedClosedRecognitionTargets.RecognizesFactor := by
 intro source H G M W oldStep window body alpha Delta s t cert parameter ha
 let leaf := OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window
 let outLeaf := OriginalTransparentMixedDirectBottom.leaf H G M W oldStep
 let qs : Fin 3 → Program 4 :=
  ![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live,run source leaf]
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 apply queryCases qs xs _
 intro beta rho ys Theta hrho hg
 have hx : (fun i => (xs i).relabel rho) =
   ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
 let xx : Fin 4 → OTerm beta :=
  ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho]
 have hh (i : Fin 3) : Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
  simpa only [hx] using hg i
 have ha' := renameInto ha rho Theta hrho
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 simp only [graph4Rename,sucRelabel,zRelabel]
 have hr := binaryRecover (InternalRawListRepeat.repeatProgram (transition source leaf))
  OriginalHereditaryLambda.path OriginalHereditaryLambda.live (ys 2) (ys 0) (ys 1) xx
  (hh 2) (hh 0) (hh 1)
 have hf := unaryRecover (finish source leaf) (run source leaf) (suc z) (ys 2) xx ha' (hh 2)
 have hnew := OriginalMixedClosedRecognitionRunProof.acceptingRun source H G M W oldStep window
  body beta Theta (ys 2) (ys 0) (ys 1) hr hf
 have hrun := binaryValue (InternalRawListRepeat.repeatProgram (transition source outLeaf))
  OriginalHereditaryLambda.path OriginalHereditaryLambda.live (ys 2) (ys 0) (ys 1) xx
  (andLeft hnew) (hh 0) (hh 1)
 exact unaryValue (finish source outLeaf) (run source outLeaf) (suc z) (ys 2) xx (andRight hnew) hrun
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionProof

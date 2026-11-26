module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRepeatSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceNormalizationProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open OriginalHereditaryLambda OriginalHereditaryLambdaChildStateProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCoordinates (oldStep : Program 4) (s t cert parameter code state : OTerm alpha)
 (hstop : Nonempty (Derivation body Delta (graph4 stop (suc z) s t cert parameter)))
 (hp : Nonempty (Derivation body Delta (graph4 path code s t cert parameter)))
 (hl : Nonempty (Derivation body Delta (graph4 live state s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (guard oldStep) (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let us : Fin 1 → OTerm alpha := ![state]
 have hn := OriginalHereditaryLambdaChildControlProof.liveNonzero state s t cert parameter hl
 have hs := atLiveValue stop (suc z) state s t cert parameter hl hstop
 let active := InternalAcceptance.branch (normalize (atState (advanceGuard oldStep)))
  (InternalAcceptance.constantZero 1) (atState childLive)
 have hf : Nonempty (Derivation body Delta (graph1 (transition oldStep) state state)) := by
  apply OriginalHereditaryLambdaChildControlProof.nonzeroBranchIntro (.projection 0)
   (InternalAcceptance.constantZero 1) _ state state us (projectionValue 0 us) hn
  exact successorBranchIntro (normalize (atState stop)) active (.projection 0)
   state z us (normalizeAccept (atState stop) us hs) (projectionValue 0 us)
 have hr := OriginalHereditaryLambdaRepeatSupportProof.fixedValue (transition oldStep) state code hf
 have hrun := binaryValue (InternalRawListRepeat.repeatProgram (transition oldStep)) path live state code state xs hr hp hl
 have hfinish : Nonempty (Derivation body Delta (graph1 finish (suc z) state)) :=
  OriginalHereditaryLambdaChildControlProof.nonzeroBranchIntro (.projection 0)
   (InternalAcceptance.constantZero 1) (atState stop) (suc z) state us (projectionValue 0 us) hn hs
 exact unaryValue finish (run oldStep) (suc z) state xs hfinish hrun

theorem stoppedGuard : OriginalHereditaryLambdaStoppedTargets.ActualStoppedGuard := by
 intro oldStep body alpha Delta s t cert parameter hstop
 let qs : Fin 2 → Program 4 := ![path,live]
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 apply queryCases qs xs _
 intro beta j ys Theta hj hg
 have hs := renameInto hstop j Theta hj
 simp only [graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hs
 simp only [graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]
 have hx : (fun i => (xs i).relabel j) = ![s.relabel j,t.relabel j,cert.relabel j,parameter.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
 have hp := hg 0
 have hl := hg 1
 rw [hx] at hp hl
 exact atCoordinates oldStep (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) (ys 0) (ys 1) hs hp hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedProof

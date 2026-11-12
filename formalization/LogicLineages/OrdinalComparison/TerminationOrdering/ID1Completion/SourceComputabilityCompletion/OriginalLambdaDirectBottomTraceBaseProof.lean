module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalHereditaryLambdaChildStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atLiveNil (source : Program 2) (leaf : Program 4) (s t cert parameter state : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (terminal source leaf) (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hpath := unaryValue InternalUnpair.left (.projection 2) z cert xs hp (projectionValue 2 xs)
 have hr := binaryValue (InternalRawListRepeat.repeatProgram (transition source leaf))
  OriginalHereditaryLambda.path OriginalHereditaryLambda.live state z state xs
  (InternalRawListRepeatSupportProof.repeatZeroValue (transition source leaf) state) hpath hl
 have hf := unaryRecover (finish source leaf) (run source leaf) (suc z) state xs ha hr
 have hn := OriginalHereditaryLambdaChildControlProof.liveNonzero state s t cert parameter hl
 have ht := OriginalHereditaryLambdaChildControlProof.nonzeroBranchElim (.projection 0)
  (InternalAcceptance.constantZero 1) (OriginalHereditaryLambda.atState (terminal source leaf))
  (suc z) state (Fin.cons state Fin.elim0) (projectionValue 0 (Fin.cons state Fin.elim0)) hn hf
 exact atLiveRecover (terminal source leaf) (suc z) state s t cert parameter hl ht

theorem terminalFields (source : Program 2) (leaf : Program 4) (s t cert parameter : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph4 (terminal source leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph2 source (suc z) s parameter ⊓
  (graph4 leaf (suc z) s t cert parameter ⊓ graph1 OriginalTransparentDirectBottom.certificateCode cert s))) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have h := conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs ht
 have hleaf := conjunctionRecover leaf OriginalTransparentDirectBottom.active xs (andRight h)
 have hs := binaryRecover source (.projection 0) (.projection 3) (suc z) s parameter xs
  (andLeft h) (projectionValue 0 xs) (projectionValue 3 xs)
 have hcode := OriginalConstructorLeafInternalProof.sameKnownLeftRecover (.projection 2)
  (.composition OriginalTransparentDirectBottom.certificateCode (fun _ : Fin 1 => .projection 0)) cert xs
  (andRight hleaf) (projectionValue 2 xs)
 have hc := unaryRecover OriginalTransparentDirectBottom.certificateCode (.projection 0) cert s xs hcode (projectionValue 0 xs)
 exact andIntro hs (andIntro (andLeft hleaf) hc)

theorem actualNilBase : OriginalLambdaDirectBottomTraceBaseTargets.ActualNilBase := by
 intro source leaf body alpha Delta s t cert parameter hp ha
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 apply programCases OriginalHereditaryLambda.live xs _
 intro beta rho Theta state hrho hl
 have hx : (fun i => (xs i).relabel rho) = ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
 rw [hx] at hl
 simp only [conjunctionRename,graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
 have hp' := renameInto hp rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [graph1Rename,zRelabel] at hp'
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 exact terminalFields source leaf (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
  (atLiveNil source leaf (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho) state hp' hl ha')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof

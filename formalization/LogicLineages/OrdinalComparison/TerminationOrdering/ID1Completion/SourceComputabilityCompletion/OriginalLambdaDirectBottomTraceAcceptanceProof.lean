module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem hopFields (source : Program 2) (leaf : Program 4) (s t cert parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph4 (hop source leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph2 source (suc z) s parameter ⊓ graph4 leaf (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have h0 := conjunctionRecover (OriginalTransparentLambdaStep.hopGuard source) leaf xs h
 have h1 := conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs (andLeft h0)
 have hs := binaryRecover source (.projection 0) (.projection 3) (suc z) s parameter xs
  (andLeft h1) (projectionValue 0 xs) (projectionValue 3 xs)
 exact andIntro hs (andRight h0)

theorem atValues (source : Program 2) (leaf : Program 4)
 (s t cert parameter code state out next head tail : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter)))
 (hp : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path code s t cert parameter)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (hr : Nonempty (Derivation body Delta (graph4 (run source leaf) out s t cert parameter)))
 (hn : Nonempty (Derivation body Delta (graph1 (transition source leaf) next state)))
 (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head code)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail code))) :
 Nonempty (Derivation body Delta (graph2 source (suc z) s parameter ⊓ graph4 leaf (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let E := eqn code z
 apply formulaCases E
 · have hz := outputTransport OriginalHereditaryLambda.path code z xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hp E)
   have hleft := unaryRecover InternalUnpair.left (.projection 2) z cert xs hz (projectionValue 2 xs)
   have hb := OriginalLambdaDirectBottomTraceBaseProof.actualNilBase source leaf body alpha (E :: Delta)
    s t cert parameter hleft (withHyp ha E)
   exact andIntro (andLeft hb) (andLeft (andRight hb))
 · have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero code head tail
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hh E.not) (withHyp ht E.not)
   have hrun := binaryRecover (InternalRawListRepeat.repeatProgram (transition source leaf))
    OriginalHereditaryLambda.path OriginalHereditaryLambda.live out code state xs
    (withHyp hr E.not) (withHyp hp E.not) (withHyp hl E.not)
   have hfinish := unaryRecover (finish source leaf) (run source leaf) (suc z) out xs
    (withHyp ha E.not) (withHyp hr E.not)
   have hd := OriginalLambdaDirectBottomTraceDescentProof.actualFrontDescent source leaf body alpha (E.not :: Delta)
    s t cert parameter code head tail state next out (withHyp hp E.not) (withHyp hl E.not)
    hc (withHyp hn E.not) hrun hfinish
   exact hopFields source leaf s t cert parameter (andLeft hd)

def queries (source : Program 2) (leaf : Program 4) : Fin 6 → Program 4 :=
 ![OriginalHereditaryLambda.path,OriginalHereditaryLambda.live,run source leaf,
 .composition (transition source leaf) (fun _ : Fin 1 => OriginalHereditaryLambda.live),
 .composition InternalListCodec.headCode (fun _ : Fin 1 => OriginalHereditaryLambda.path),
 .composition InternalListCodec.tailCode (fun _ : Fin 1 => OriginalHereditaryLambda.path)]

theorem actualAcceptance : OriginalLambdaDirectBottomTraceAcceptanceTargets.ActualAcceptance := by
 intro source leaf body alpha Delta s t cert parameter ha
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 apply queryCases (queries source leaf) xs _
 intro beta rho ys Theta hrho hg
 have hx : (fun i => (xs i).relabel rho) = ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
 have ha' := renameInto ha rho Theta hrho
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 simp only [conjunctionRename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
 let xx : Fin 4 → OTerm beta := ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho]
 have hh (i : Fin 6) : Nonempty (Derivation body Theta (programGraph (queries source leaf i) (ys i) xx)) := by
  simpa only [hx] using hg i
 have hp := hh 0
 have hl := hh 1
 have hr := hh 2
 have hn := unaryRecover (transition source leaf) OriginalHereditaryLambda.live (ys 3) (ys 1) xx (hh 3) hl
 have hhead := unaryRecover InternalListCodec.headCode OriginalHereditaryLambda.path (ys 4) (ys 0) xx (hh 4) hp
 have htail := unaryRecover InternalListCodec.tailCode OriginalHereditaryLambda.path (ys 5) (ys 0) xx (hh 5) hp
 exact atValues source leaf (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
  (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) ha' hp hl hr hn hhead htail
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceFrontQueryProof
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
open OriginalMixedDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof-only query packaging of the already checked front descent. -/
theorem frontCases (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail : OTerm alpha) (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) s t cert parameter)))
 (nextCase : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (state next out : OTerm beta),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph4 OriginalHereditaryLambda.live state (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) →
   Nonempty (Derivation body Theta
    ((graph1 (OriginalHereditaryLambda.atState (lambdaHop source leaf)) (suc z) state ⊓
      graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state) ⊔
     (graph1 (OriginalHereditaryLambda.atState (applicationHop source leaf)) (suc z) state ⊓
      graph1 (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive) next state))) →
   Nonempty (Derivation body Theta (InternalRawListRepeat.repeatGraph (transition source leaf) out (tail.relabel rho) next)) →
   Nonempty (Derivation body Theta (graph1 (finish source leaf) (suc z) out)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let qs : Fin 3 → Program 4 := ![OriginalHereditaryLambda.live,run source leaf,
   .composition (transition source leaf) (fun _ : Fin 1 => OriginalHereditaryLambda.live)]
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hg
 have hx : (fun i => (xs i).relabel rho) = ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))) i
 let xx : Fin 4 → OTerm beta := ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho]
 have hh (i : Fin 3) : Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
  simpa only [hx] using hg i
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [graph1Rename] at hp'
 simp only [graph2Rename] at hc'
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 have hpath := unaryValue InternalUnpair.left (.projection 2) (code.relabel rho) (cert.relabel rho) xx
   hp' (projectionValue (2 : Fin 4) xx)
 have hl := hh 0
 have hr := hh 1
 have hn := unaryRecover (transition source leaf) OriginalHereditaryLambda.live (ys 2) (ys 0) xx (hh 2) hl
 have hrun := binaryRecover (InternalRawListRepeat.repeatProgram (transition source leaf))
   OriginalHereditaryLambda.path OriginalHereditaryLambda.live (ys 1) (code.relabel rho) (ys 0) xx hr hpath hl
 have hf := unaryRecover (finish source leaf) (run source leaf) (suc z) (ys 1) xx ha' hr
 have hd := OriginalMixedDirectBottomTraceDescentProof.actualFrontDescent source leaf body beta Theta
   (code.relabel rho) (head.relabel rho) (tail.relabel rho) (ys 0) (ys 2) (ys 1)
   hc' hn hrun hf
 exact nextCase beta rho Theta (ys 0) (ys 2) (ys 1) hrho hl (andLeft hd) (andRight hd) hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceFrontQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceFrontQueryProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceFrontQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerSuccessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open OriginalHereditaryLambdaChildStateProof (atLiveRecover)
open OriginalMixedDirectBottomTrace
open ScannerFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem structuralNilContradiction (state s t cert : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)))
 (hg : Nonempty (Derivation body Delta
  (graph1 InternalApplicationStepPeel.structuralGuard (suc z) state))) :
 Nonempty (Derivation body Delta (⊥ : Formula alpha)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
 have hpath := unaryValue InternalUnpair.left step z cert xs hp
  (andRight (andRight (edgeSelectors state s t cert he)))
 have hn := andLeft (conjunctionRecover InternalApplicationStepPeel.nonemptyPath _ xs hg)
 have hz := zeroBranchElim InternalApplicationStepPeel.rawPath (InternalAcceptance.constantZero 1)
  (InternalLessThan.constantOne 1) (suc z) xs hpath hn
 obtain ⟨heq⟩ := valueUnique (InternalAcceptance.constantZero 1) (suc z) z xs hz
  (constantZeroValue xs)
 exact ⟨sucNeZeroApply heq⟩

theorem recognizedAppChild (S : Program 2) (leaf : Program 4)
 (s t cert parameter childS childT childCert state next out tail newState : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode newState childS childT childCert)))
 (hs : Nonempty (Derivation body Delta (graph4
  OriginalTransparentApplicationFunctionDefinitions.sourceFunction childS s t cert parameter)))
 (ht : Nonempty (Derivation body Delta (graph4
  OriginalTransparentApplicationFunctionDefinitions.targetFunction childT s t cert parameter)))
 (hk : Nonempty (Derivation body Delta (graph4
  OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert parameter)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (hb : Nonempty (Derivation body Delta
  (graph1 (OriginalHereditaryLambda.atState (applicationHop S leaf)) (suc z) state ⊓
   graph1 (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive) next state)))
 (hr : Nonempty (Derivation body Delta
  (InternalRawListRepeat.repeatGraph (transition S leaf) out tail next)))
 (hf : Nonempty (Derivation body Delta (graph1 (finish S leaf) (suc z) out))) :
 Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) newState parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let ps : Fin 4 → Program 4 := ![
  OriginalTransparentApplicationFunctionDefinitions.sourceFunction,
  OriginalTransparentApplicationFunctionDefinitions.targetFunction,
  OriginalTransparentApplicationFunctionDefinitions.childCertificate,
  OriginalTransparentApplicationFunctionDefinitions.childParameter]
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,parameter]
 have hvalues : ∀ i : Fin 4, Nonempty (Derivation body Delta (programGraph (ps i) (ys i) xs)) := by
  intro i
  exact Fin.cases hs (Fin.cases ht (Fin.cases hk
   (Fin.cases (projectionValue 3 xs) (fun j => Fin.elim0 j)))) i
 have hchild := atLiveRecover OriginalTransparentApplicationFunctionDefinitions.childLive
  next state s t cert parameter hl (andRight hb)
 have hnext := compositionRecover OriginalHereditaryLambda.live ps next xs ys hchild hvalues
 have ha := OriginalMixedDirectBottomTraceChildInductionProof.recognizedFromRun
  S leaf childS childT childCert parameter tail next out hp hnext hr hf
 exact wireAccepted S leaf newState childS childT childCert parameter he ha

/-- The original structural tag excludes the first lambda alternative.
Only the actual application alternative supplies the common accepted tail. -/
theorem successAtCons (S : Program 2) (leaf : Program 4)
 (s t cert parameter childS childT childCert path head tail newState : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode newState childS childT childCert)))
 (hs : Nonempty (Derivation body Delta (graph4
  OriginalTransparentApplicationFunctionDefinitions.sourceFunction childS s t cert parameter)))
 (ht : Nonempty (Derivation body Delta (graph4
  OriginalTransparentApplicationFunctionDefinitions.targetFunction childT s t cert parameter)))
 (hk : Nonempty (Derivation body Delta (graph4
  OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert parameter)))
 (hchildPath : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left path cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (ha : Nonempty (Derivation body Delta
  (graph4 (recognizes S leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) newState parameter)) := by
 apply OriginalMixedDirectBottomTraceFrontQueryProof.frontCases S leaf
  s t cert parameter path head tail _ hp hc ha
 intro beta rho Theta state next out hrho hl hb hr hf
 simp only [graph2Rename,sucRelabel,zRelabel]
 have he' := renameInto he rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 have ht' := renameInto ht rho Theta hrho
 have hk' := renameInto hk rho Theta hrho
 have hp' := renameInto hchildPath rho Theta hrho
 have htag' := renameInto htag rho Theta hrho
 simp only [graph3Rename] at he'
 simp only [graph4Rename] at hs' ht' hk'
 simp only [graph1Rename] at hp'
 simp only [graph1Rename,sucRelabel,zRelabel] at htag'
 let A := graph1 (OriginalHereditaryLambda.atState (lambdaHop S leaf)) (suc z) state ⊓
  graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state
 let B := graph1 (OriginalHereditaryLambda.atState (applicationHop S leaf)) (suc z) state ⊓
  graph1 (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive) next state
 have hA : Nonempty (Derivation body (A :: Theta)
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) (newState.relabel rho) (parameter.relabel rho))) := by
  have h : Nonempty (Derivation body (A :: Theta) A) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hhop := atLiveRecover (lambdaHop S leaf) (suc z) state
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
   (withHyp hl A) (andLeft h)
  have hguard := andLeft (conjunctionRecover (OriginalTransparentLambdaStep.hopGuard S) leaf
   ![s.relabel rho,t.relabel rho,cert.relabel rho,parameter.relabel rho] hhop)
  obtain ⟨hn⟩ := OriginalTransparentMixedPathApplicationControlProof.lambdaGuardReject S
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho) (withHyp htag' A)
  obtain ⟨hg⟩ := hguard
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn hg)⟩
 have hB := recognizedAppChild S leaf
  (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
  (childS.relabel rho) (childT.relabel rho) (childCert.relabel rho)
  state next out (tail.relabel rho) (newState.relabel rho)
  (withHyp he' B) (withHyp hs' B) (withHyp ht' B) (withHyp hk' B) (withHyp hp' B)
  (withHyp hl B) (show Nonempty (Derivation body (B :: Theta) B) from
   ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hr B) (withHyp hf B)
 obtain ⟨hA⟩ := hA
 obtain ⟨hB⟩ := hB
 obtain ⟨hb⟩ := hb
 exact ⟨InternalBetaTotalityProof.disjunctionElimination hb
  (Derivation.implicationIntroduction hA) (Derivation.implicationIntroduction hB)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerSuccessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerSuccessProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerSuccessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalParameterizedApplicationStepChecker
open InternalParameterizedApplicationResultStack (liftP)
open InternalParameterizedApplicationResultStackWiringProof (liftRecover)
open InternalParameterizedApplicationStepCheckerGraphProof (edgeStateValue)
open ScannerFieldsProof ScannerSuccessProof
open OriginalMixedDirectBottomTrace (recognizes)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atEdgeValue (q : Program 1) (value state s t cert parameter : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hq : Nonempty (Derivation body Delta (graph1 q value state))) :
 Nonempty (Derivation body Delta (graph4
  (OriginalTransparentApplicationFunctionDefinitions.atEdge q) value s t cert parameter)) :=
 unaryValue q OriginalTransparentApplicationFunctionDefinitions.edge value state ![s,t,cert,parameter]
  hq (edgeStateValue state s t cert parameter he)

theorem rawFieldsAtCons (S : Program 2) (leaf : Program 4)
 (state newState s t cert parameter childS childT childCert path head tail : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hne : Nonempty (Derivation body Delta (graph3 edgeCode newState childS childT childCert)))
 (hs : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.functionCode childS state)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.targetFunctionCode childT state)))
 (hk : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.peeledStep childCert state)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left path cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hg : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.structuralGuard (suc z) state)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes S leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) newState parameter)) :=
 successAtCons S leaf s t cert parameter childS childT childCert path head tail newState hne
  (atEdgeValue InternalApplicationStepPeel.functionCode childS state s t cert parameter he hs)
  (atEdgeValue InternalApplicationStepPeel.targetFunctionCode childT state s t cert parameter he ht)
  (atEdgeValue InternalApplicationStepPeel.peeledStep childCert state s t cert parameter he hk)
  (peeledCertificatePath state s t cert childCert path head tail he hp hc hk)
  (sourceTagTwo state s t cert he hg) hp hc ha

theorem rawFieldsAtPath (S : Program 2) (leaf : Program 4)
 (state newState s t cert parameter childS childT childCert path : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hne : Nonempty (Derivation body Delta (graph3 edgeCode newState childS childT childCert)))
 (hs : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.functionCode childS state)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.targetFunctionCode childT state)))
 (hk : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.peeledStep childCert state)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left path cert)))
 (hg : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.structuralGuard (suc z) state)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes S leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) newState parameter)) := by
 apply OriginalContextInsertionLengthProof.listCases path _
 · have hz : Nonempty (Derivation body (eqn path z :: Delta) (eqn path z)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hpz := outputTransport InternalUnpair.left path z (Fin.cons cert Fin.elim0)
    hz (withHyp hp (eqn path z))
   obtain ⟨hfalse⟩ := structuralNilContradiction state s t cert
    (withHyp he (eqn path z)) hpz (withHyp hg (eqn path z))
   exact ⟨Derivation.explosion hfalse⟩
 · intro beta rho Theta head tail hrho hc
   simp only [graph2Rename,sucRelabel,zRelabel]
   have he' := renameInto he rho Theta hrho
   have hne' := renameInto hne rho Theta hrho
   have hs' := renameInto hs rho Theta hrho
   have ht' := renameInto ht rho Theta hrho
   have hk' := renameInto hk rho Theta hrho
   have hp' := renameInto hp rho Theta hrho
   have hg' := renameInto hg rho Theta hrho
   have ha' := renameInto ha rho Theta hrho
   simp only [graph3Rename] at he' hne'
   simp only [graph1Rename] at hs' ht' hk' hp'
   simp only [graph1Rename,sucRelabel,zRelabel] at hg'
   simp only [graph4Rename,sucRelabel,zRelabel] at ha'
   exact rawFieldsAtCons S leaf (state.relabel rho) (newState.relabel rho)
    (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
    (childS.relabel rho) (childT.relabel rho) (childCert.relabel rho) (path.relabel rho) head tail
    he' hne' hs' ht' hk' hp' hc hg' ha'

/-- All fields of the actual peeled state are queried once and recovered
through the literal original edgeCode composition. -/
theorem successful (S : Program 2) (leaf : Program 4)
 (state next s t cert parameter : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hg : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.structuralGuard (suc z) state)))
 (hn : Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.peeledState next state)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes S leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) next parameter)) := by
 let qs : Fin 4 → Program 1 := ![InternalApplicationStepPeel.rawPath,
  InternalApplicationStepPeel.functionCode,InternalApplicationStepPeel.targetFunctionCode,
  InternalApplicationStepPeel.peeledStep]
 apply queryCases qs (Fin.cons state Fin.elim0) _
 intro beta rho ys Theta hrho hq
 simp only [graph2Rename,sucRelabel,zRelabel]
 simp only [consTermRename,emptyRename] at hq
 have he' := renameInto he rho Theta hrho
 have hg' := renameInto hg rho Theta hrho
 have hn' := renameInto hn rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [graph3Rename] at he'
 simp only [graph1Rename,sucRelabel,zRelabel] at hg'
 simp only [graph1Rename] at hn'
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel rho) Fin.elim0
 have hp := unaryRecover InternalUnpair.left step (ys 0) (cert.relabel rho) xs (hq 0)
  (andRight (andRight (edgeSelectors (state.relabel rho) (s.relabel rho)
   (t.relabel rho) (cert.relabel rho) he')))
 have hnew := compositionRecover edgeCode
  ![InternalApplicationStepPeel.functionCode,InternalApplicationStepPeel.targetFunctionCode,
   InternalApplicationStepPeel.peeledStep] (next.relabel rho) xs ![ys 1,ys 2,ys 3] hn'
  (by intro i; exact Fin.cases (hq 1) (Fin.cases (hq 2) (Fin.cases (hq 3) (fun j => Fin.elim0 j))) i)
 exact rawFieldsAtPath S leaf (state.relabel rho) (next.relabel rho)
  (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho)
  (ys 1) (ys 2) (ys 3) (ys 0) he' hnew (hq 1) (hq 2) (hq 3) hp hg' ha'

/-- Concrete one-step supplier, including failed arbitrary endpoint tests.
Both source acceptance and lambda-first priority are paid by the actual
recognizer, never supplied as external scanner premises. -/
theorem scannerPreservesRecognition : ScannerTargets.ScannerPreservesRecognition := by
 intro S leaf endpoint body alpha Delta state next parameter ht ha
 apply edgeCases state _
 intro beta rho Theta s t cert hrho he
 simp only [graph2Rename,sucRelabel,zRelabel]
 have ht' := renameInto ht rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [graph2Rename] at ht'
 simp only [graph2Rename,sucRelabel,zRelabel] at ha'
 let xs : Fin 2 → OTerm beta := ![state.relabel rho,parameter.relabel rho]
 let A := graph2 (guardP endpoint) (suc z) (state.relabel rho) (parameter.relabel rho)
 apply formulaCases A
 · have hg : Nonempty (Derivation body (A :: Theta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hparts := conjunctionRecover (liftP InternalApplicationStepPeel.structuralGuard)
    (endpointAtP endpoint) xs hg
   have hstruct := liftRecover InternalApplicationStepPeel.structuralGuard (suc z)
    (state.relabel rho) (parameter.relabel rho) (andLeft hparts)
   have hnew := successorBranchElim (guardP endpoint) (.projection 0)
    (liftP InternalApplicationStepPeel.peeledState) (next.relabel rho) z xs hg (withHyp ht' A)
   have hpeeled := liftRecover InternalApplicationStepPeel.peeledState (next.relabel rho)
    (state.relabel rho) (parameter.relabel rho) hnew
   exact successful S leaf (state.relabel rho) (next.relabel rho) s t cert (parameter.relabel rho)
    (withHyp he A) hstruct hpeeled
    (wireRecoverAccepted S leaf (state.relabel rho) s t cert (parameter.relabel rho)
     (withHyp he A) (withHyp ha' A))
 · have hn : Nonempty (Derivation body (A.not :: Theta) A.not) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hg := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
    (liftP InternalApplicationStepPeel.structuralGuard) (endpointAtP endpoint) xs hn
   have hp := zeroBranchElim (guardP endpoint) (.projection 0)
    (liftP InternalApplicationStepPeel.peeledState) (next.relabel rho) xs hg (withHyp ht' A.not)
   obtain ⟨heq⟩ := valueUnique (.projection (0 : Fin 2)) (next.relabel rho) (state.relabel rho)
    xs hp (projectionValue 0 xs)
   exact headTransport (ScannerTargets.stateRecognizes S leaf) (suc z) (state.relabel rho)
    (next.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
    ⟨symm heq⟩ (withHyp ha' A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerStepProof

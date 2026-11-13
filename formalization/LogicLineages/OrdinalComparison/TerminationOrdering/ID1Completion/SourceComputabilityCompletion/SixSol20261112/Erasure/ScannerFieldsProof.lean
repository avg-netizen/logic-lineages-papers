module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.SelectedNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceChildInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalParameterizedApplicationResultStackWiringProof (wireValue wireRecover)
open InternalParameterizedApplicationStepCheckerSyntaxProof (appendParameterThree)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem edgeCases (state : OTerm alpha) (psi : Formula alpha)
 (k : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
  (s t cert : OTerm beta),
  (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
  Nonempty (Derivation body Theta (graph3 edgeCode (state.relabel rho) s t cert)) →
  Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 apply queryCases (![source,target,step] : Fin 3 → Program 1) (Fin.cons state Fin.elim0) _
 intro beta rho ys Theta hrho hq
 simp only [consTermRename,emptyRename] at hq
 exact k beta rho Theta (ys 0) (ys 1) (ys 2) hrho
  (edgeReconstruction (state.relabel rho) (ys 0) (ys 1) (ys 2)
   (andIntro (hq 0) (andIntro (hq 1) (hq 2))))

theorem wireAccepted (S : Program 2) (leaf : Program 4)
 (state s t cert parameter : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (ha : Nonempty (Derivation body Delta
  (graph4 (OriginalMixedDirectBottomTrace.recognizes S leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) state parameter)) := by
 exact wireValue (OriginalMixedDirectBottomTrace.recognizes S leaf) ![source,target,step]
  (suc z) state parameter (Fin.cons s (Fin.cons t (Fin.cons cert Fin.elim0)))
  (by simpa only [appendParameterThree] using ha) (SelectedNilProof.selectorsAt s t cert state he)

theorem wireRecoverAccepted (S : Program 2) (leaf : Program 4)
 (state s t cert parameter : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (ha : Nonempty (Derivation body Delta
  (graph2 (ScannerTargets.stateRecognizes S leaf) (suc z) state parameter))) :
 Nonempty (Derivation body Delta
  (graph4 (OriginalMixedDirectBottomTrace.recognizes S leaf) (suc z) s t cert parameter)) := by
 have h := wireRecover (OriginalMixedDirectBottomTrace.recognizes S leaf) ![source,target,step]
  (suc z) state parameter (Fin.cons s (Fin.cons t (Fin.cons cert Fin.elim0))) ha (SelectedNilProof.selectorsAt s t cert state he)
 simpa only [appendParameterThree] using h

/-- Original structural acceptance forces tag two at the real source.
Composition wiring is exposed internally, so no associativity of Program
ASTs or source-lambda rejection is assumed. -/
theorem sourceTagTwo (state s t cert : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hg : Nonempty (Derivation body Delta
  (graph1 InternalApplicationStepPeel.structuralGuard (suc z) state))) :
 Nonempty (Derivation body Delta
  (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s)) := by
 have hrest := andRight (conjunctionRecover InternalApplicationStepPeel.nonemptyPath _
  (Fin.cons state Fin.elim0) hg)
 have htag := andLeft (conjunctionRecover
  (InternalApplicationStepPeel.same (InternalApplicationStepPeel.constructorTag source) (two 1)) _
  (Fin.cons state Fin.elim0) (andRight (conjunctionRecover
   (InternalApplicationStepPeel.same InternalApplicationStepPeel.pathHead (two 1)) _
   (Fin.cons state Fin.elim0) hrest)))
 have ht := sameRightRecover (InternalApplicationStepPeel.constructorTag source) (two 1)
  (suc (suc z)) (Fin.cons state Fin.elim0) htag (twoValue (Fin.cons state Fin.elim0))
 apply programCases InternalUnpair.right (Fin.cons s Fin.elim0) _
 intro beta rho Theta payload hrho hp
 simp only [graph1Rename,sucRelabel,zRelabel]
 simp only [consTermRename,emptyRename] at hp
 have he' := renameInto he rho Theta hrho
 simp only [graph3Rename] at he'
 have ht' := renameInto ht rho Theta hrho
 simp only [programRename,sucRelabel,zRelabel,consTermRename,emptyRename] at ht'
 let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel rho) Fin.elim0
 have hs := andLeft (edgeSelectors (state.relabel rho) (s.relabel rho)
  (t.relabel rho) (cert.relabel rho) he')
 have hright := unaryValue InternalUnpair.right source payload (s.relabel rho) xs hp hs
 have hleft := unaryRecover InternalUnpair.left (rightOf source) (suc (suc z)) payload xs ht' hright
 exact unaryValue InternalUnpair.left (rightOf (.projection 0)) (suc (suc z)) payload
  (Fin.cons (s.relabel rho) Fin.elim0) hleft
  (unaryValue InternalUnpair.right (.projection 0) payload (s.relabel rho)
   (Fin.cons (s.relabel rho) Fin.elim0) hp (projectionValue (body := body) (Gamma := Theta) 0 (Fin.cons (s.relabel rho) Fin.elim0)))

/-- The peeled certificate's left coordinate is the ACTUAL old path tail.
No supplied certificate-prefix equation is required for this observer law. -/
theorem peeledCertificatePath (state s t cert childCert path head tail : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edgeCode state s t cert)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left path cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hk : Nonempty (Derivation body Delta
  (graph1 InternalApplicationStepPeel.peeledStep childCert state))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)) := by
 let q := rightOf step
 apply programCases q (Fin.cons state Fin.elim0) _
 intro beta rho Theta payload hrho hq
 simp only [graph1Rename]
 simp only [consTermRename,emptyRename] at hq
 have he' := renameInto he rho Theta hrho
 have hp' := renameInto hp rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hk' := renameInto hk rho Theta hrho
 simp only [graph3Rename] at he'
 simp only [graph1Rename] at hp' hk'
 simp only [graph2Rename] at hc'
 let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel rho) Fin.elim0
 have hpath := unaryValue InternalUnpair.left step (path.relabel rho) (cert.relabel rho) xs hp'
  (andRight (andRight (edgeSelectors (state.relabel rho) (s.relabel rho)
   (t.relabel rho) (cert.relabel rho) he')))
 have ht := unaryValue InternalListCodec.tailCode InternalApplicationStepPeel.rawPath
  (tail.relabel rho) (path.relabel rho) xs
  (andLeft (andRight (InternalListCodecSupportProof.consDestruction
   (path.relabel rho) (head.relabel rho) (tail.relabel rho) hc'))) hpath
 have hpair := binaryRecover InternalPairing.pairing InternalApplicationStepPeel.pathTail q
  (childCert.relabel rho) (tail.relabel rho) payload xs hk' ht hq
 exact pairLeft (childCert.relabel rho) (tail.relabel rho) payload hpair
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.ScannerFieldsProof

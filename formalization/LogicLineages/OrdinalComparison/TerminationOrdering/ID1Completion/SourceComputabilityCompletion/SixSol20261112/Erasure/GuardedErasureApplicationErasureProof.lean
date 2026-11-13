module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open OriginalMixedClosedApplicationErasureDefinitions
open OriginalMixedExistentialCongruenceSupportProof (resultRename)
open OriginalMixedClosedApplicationErasureQueryProof (childIHRename queries)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedErasureFinalGraphsProof GuardedErasurePackingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

/-- Reuses the original raw application erasure/type equations and original
child-validity proof. The sole new operation lifts the SAME child C∧W witness. -/
theorem atCoordinates (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3) :
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newChildS newChildT newArg newParam erasedType cutoff gamma extended context : OTerm alpha),
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap oldChildS oldArg oldS)) →
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop (literalSource p H G W)
  oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow)) →
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (numeral 1) oldS oldT oldCert oldParam)) →
 Nonempty (Derivation body Delta (graph4 (OriginalMixedDirectBottomTrace.recognizes (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) (numeral 1) oldChildS oldChildT oldChildCert oldParam)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newChildS erasedType cutoff oldChildS)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newChildT erasedType cutoff oldChildT)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newArg erasedType cutoff oldArg)) →
 OriginalMixedClosedApplicationErasureDefinitions.ChildIH body Delta (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) (literalSource p H G W)
  oldChildS oldChildT oldChildCert oldParam erasedType cutoff context →
 Nonempty (Derivation body Delta (OriginalExistentialRankResultDefinitions.Result (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) newS newT newParam oldS oldT)) := by
 intro body alpha Delta oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newChildS newChildT newArg newParam erasedType cutoff gamma extended context hctor hh hparent hrec hi hop hnp hes het hecs hect hea ih
 have hs := andLeft hh
 have happS := andLeft (andRight hh)
 have happT := andLeft (andRight (andRight hh))
 have harrow := andLeft (andRight (andRight (andRight hh)))
 have htypeS := andLeft (andRight (andRight (andRight (andRight hh))))
 have htypeT := andLeft (andRight (andRight (andRight (andRight (andRight hh)))))
 have htypeA := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hsourceChild := andLeft (OriginalPackedSourceApplicationFieldsProof.sourceChildren H G (member p) W
  arrow domain codomain fp ap oldChildS oldArg oldS oldParam hctor hs)
 have hchild : Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (numeral 1) oldChildS oldChildT oldChildCert oldParam)) := by
  obtain ⟨law⟩ := OriginalTransparentMixedPathApplicationPrefixProof.hop (literalSource p H G W)
   (OriginalTransparentDirectBottom.refined (literalSource p H G W) p.oldStep)
   oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow (numeral 1) hh
  obtain ⟨hparent⟩ := hparent
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft law) hparent⟩
 have hsourceE := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G (member p) W
  oldS newS erasedType cutoff gamma extended context oldParam newParam hi hes hop hnp hs
 have newAppS := OriginalPackedApplicationErasureProof.applicationErasure oldS domain codomain oldChildS oldArg
  newS newChildS newArg erasedType cutoff happS hes hecs hea
 have newAppT := OriginalPackedApplicationErasureProof.applicationErasure oldT domain codomain oldChildT oldArg
  newT newChildT newArg erasedType cutoff happT het hect hea
 have newTypeS := OriginalPackedApplicationErasureProof.eraseTypeCopy oldChildS newChildS arrow erasedType cutoff htypeS hecs
 have newTypeT := OriginalPackedApplicationErasureProof.eraseTypeCopy oldChildT newChildT arrow erasedType cutoff htypeT hect
 have newTypeA := OriginalPackedApplicationErasureProof.eraseTypeCopy oldArg newArg domain erasedType cutoff htypeA hea
 have frame : Nonempty (Derivation body Delta (OriginalMixedExistentialCongruenceDefinitions.ApplicationFrame
  (literalSource p H G W) newS newT newParam newChildS newChildT newArg domain codomain arrow)) :=
  andIntro hsourceE (andIntro newAppS (andIntro newAppT (andIntro harrow (andIntro newTypeS (andIntro newTypeT newTypeA)))))
 have childResult := ih alpha id Delta
  (fun f hf => by simpa only [InternalFiniteBlocksSubstitutionProof.renameIdentity] using hf)
  newChildS newChildT newParam gamma extended
  (by simpa only [Term.relabel_id,OriginalTransparentMixedDirectBottom.source] using hsourceChild)
  (by simpa only [Term.relabel_id] using hchild)
  (by simpa only [Term.relabel_id] using hop)
  (by simpa only [Term.relabel_id] using hnp)
  (by simpa only [Term.relabel_id] using hi)
  (by simpa only [Term.relabel_id] using hecs)
  (by simpa only [Term.relabel_id] using hect)
 have both := OriginalMixedTraceErasedValidityProof.actualBothErasedSource H G (member p) W p.oldStep body alpha Delta
  oldChildS oldChildT oldChildCert oldParam newParam gamma extended erasedType cutoff context newChildS newChildT
  (by simpa only [OriginalTransparentMixedDirectBottom.source] using hsourceChild) hrec hi hop hnp hecs hect
 have hend := OriginalMixedLiteralEndpointFrameProof.atFrame H G (member p) W newS newT newParam newChildS newChildT newArg domain codomain arrow frame (andRight both)
 apply GuardedErasureApplicationCongruenceProof.actualApplication p H G W P
  newS newT newParam newChildS newChildT newArg domain codomain arrow oldS oldT oldChildS oldChildT oldArg
  frame hend happS happT
 simpa only [Term.relabel_id] using childResult

theorem atFields (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3) :
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newParam erasedType cutoff gamma extended context : OTerm alpha),
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap oldChildS oldArg oldS)) →
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop (literalSource p H G W)
  oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow)) →
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (numeral 1) oldS oldT oldCert oldParam)) →
 Nonempty (Derivation body Delta (graph4 (OriginalMixedDirectBottomTrace.recognizes (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) (numeral 1) oldChildS oldChildT oldChildCert oldParam)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)) →
 OriginalMixedClosedApplicationErasureDefinitions.ChildIH body Delta (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) (literalSource p H G W)
  oldChildS oldChildT oldChildCert oldParam erasedType cutoff context →
 Nonempty (Derivation body Delta (OriginalExistentialRankResultDefinitions.Result (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) newS newT newParam oldS oldT)) := by
 intro body alpha Delta oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newParam erasedType cutoff gamma extended context hctor hh hparent hrec hi hop hnp hes het ih
 let xs : Fin 5 → OTerm alpha := ![oldChildS,oldChildT,oldArg,erasedType,cutoff]
 apply queryCases queries xs _
 intro beta j ys Theta hj hq
 rw [resultRename]
 have hctor' := renameInto hctor j Theta hj
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hctor'
 have hh' := renameInto hh j Theta hj
 simp only [OriginalTransparentMixedPathInternalDefinitions.ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
  GuardedSourceSyntaxProof.numeralRename] at hh'
 have hparent' := renameInto hparent j Theta hj
 simp only [graph4Rename,GuardedSourceSyntaxProof.numeralRename] at hparent'
 have hrec' := renameInto hrec j Theta hj
 simp only [graph4Rename,GuardedSourceSyntaxProof.numeralRename] at hrec'
 have hi' := renameInto hi j Theta hj
 rw [OriginalContextInsertionSyntaxProof.insertRename] at hi'
 have hop' := renameInto hop j Theta hj
 have hnp' := renameInto hnp j Theta hj
 rw [graph2Rename] at hop' hnp'
 have hes' := renameInto hes j Theta hj
 have het' := renameInto het j Theta hj
 rw [graph3Rename] at hes' het'
 have ih' := childIHRename (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W))
  (literalSource p H G W) oldChildS oldChildT oldChildCert oldParam erasedType cutoff context j Theta hj ih
 let xx : Fin 5 → OTerm beta := ![oldChildS.relabel j,oldChildT.relabel j,oldArg.relabel j,erasedType.relabel j,cutoff.relabel j]
 have heq : (fun i => (xs i).relabel j) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [heq] at hq
 have hcs := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.projection 3) (.projection 4) (.projection 0) (ys 0) (erasedType.relabel j) (cutoff.relabel j) (oldChildS.relabel j) xx (hq 0)
  (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 0 xx)
 have hct := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.projection 3) (.projection 4) (.projection 1) (ys 1) (erasedType.relabel j) (cutoff.relabel j) (oldChildT.relabel j) xx (hq 1)
  (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 1 xx)
 have hca := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw
  (.projection 3) (.projection 4) (.projection 2) (ys 2) (erasedType.relabel j) (cutoff.relabel j) (oldArg.relabel j) xx (hq 2)
  (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 2 xx)
 exact atCoordinates p H G W P body beta Theta
  (oldS.relabel j) (oldT.relabel j) (oldCert.relabel j) (oldParam.relabel j) (oldChildS.relabel j) (oldChildT.relabel j)
  (oldChildCert.relabel j) (oldArg.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j) (fp.relabel j) (ap.relabel j)
  (newS.relabel j) (newT.relabel j) (ys 0) (ys 1) (ys 2) (newParam.relabel j) (erasedType.relabel j) (cutoff.relabel j)
  (gamma.relabel j) (extended.relabel j) (context.relabel j) hctor' hh' hparent' hrec' hi' hop' hnp' hes' het' hcs hct hca ih'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationErasureProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnStackContentSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualConsContent : OriginalListReturnContentTargets.ConsContent := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out outRest outOld suffix childTail first second value
  hstate hwork hframe hrole hraw htag hchildren hcount hlength hreverse happend hc1 hc2 hactual hout hstack
 let v : Program 5 := .composition OriginalHereditaryReturn.returnArgumentsCons ![.projection 0,.projection 1,.projection 2]
 let s : Program 5 := consOf v (.projection 3)
 let o : Program 5 := pairOf (.projection 4) s
 let qs : Fin 3 → Program 5 := ![v,s,o]
 let xs : Fin 5 → OTerm alpha := ![raw,first,second,old,rest]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hq
 let xx : Fin 5 → OTerm beta := ![raw.relabel j,first.relabel j,second.relabel j,old.relabel j,rest.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [hx] at hq
 have hstate' := renameInto hstate j Theta hinc
 have hwork' := renameInto hwork j Theta hinc
 have hframe' := renameInto hframe j Theta hinc
 have hrole' := renameInto hrole j Theta hinc
 have hraw' := renameInto hraw j Theta hinc
 have htag' := renameInto htag j Theta hinc
 have hchildren' := renameInto hchildren j Theta hinc
 have hcount' := renameInto hcount j Theta hinc
 have hlength' := renameInto hlength j Theta hinc
 have hreverse' := renameInto hreverse j Theta hinc
 have happend' := renameInto happend j Theta hinc
 have hc1' := renameInto hc1 j Theta hinc
 have hc2' := renameInto hc2 j Theta hinc
 have hactual' := renameInto hactual j Theta hinc
 have hout' := renameInto hout j Theta hinc
 have hstack' := renameInto hstack j Theta hinc
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,zRelabel,sucRelabel] at hstate' hwork' hframe' hrole' hraw' htag' hchildren' hcount' hlength' hreverse' happend' hc1' hc2' hactual' hout' hstack'
 have hv := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalHereditaryReturn.returnArgumentsCons
  (.projection 0) (.projection 1) (.projection 2) (ys 0) (raw.relabel j) (first.relabel j) (second.relabel j) xx
  (hq 0) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 2 xx)
 have hs := binaryRecover InternalListCodec.consCode v (.projection 3) (ys 1) (ys 0) (old.relabel j) xx
  (hq 1) (hq 0) (projectionValue 3 xx)
 have ho := binaryRecover InternalPairing.pairing (.projection 4) s (ys 2) (rest.relabel j) (ys 1) xx
  (hq 2) (projectionValue 4 xx) (hq 1)
 have hforward := OriginalRestoredListReturnProof.listCons R body beta Theta
  (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j)
  (raw.relabel j) (rawPayload.relabel j) (count.relabel j) (row.relabel j) (reversed.relabel j) (old.relabel j)
  (ys 1) (ys 2) (suffix.relabel j) (childTail.relabel j) (first.relabel j) (second.relabel j) (ys 0)
  hstate' hwork' hframe' hrole' hraw' htag' hchildren' hcount' hlength' hreverse' happend' hc1' hc2' hv hs ho
 have restored := OriginalReturnStackContentSupportProof.restoreFields (OriginalHereditaryReturnStep.step R)
  (input.relabel j) (ys 2) (out.relabel j) (rest.relabel j) (outRest.relabel j) (ys 1) (stack.relabel j)
  (ys 0) (value.relabel j) (old.relabel j) (outOld.relabel j) hforward hactual' ho hs hout' hstack'
 have hvalue := outputTransport OriginalHereditaryReturn.returnArgumentsCons (ys 0) (value.relabel j)
  (Fin.cons (raw.relabel j) (Fin.cons (first.relabel j) (Fin.cons (second.relabel j) Fin.elim0))) (andLeft restored) hv
 obtain ⟨hr⟩ := andLeft (andRight restored)
 obtain ⟨hold⟩ := andRight (andRight restored)
 simp only [conjunctionRename,graph3Rename,eqnRelabel]
 exact andIntro hvalue (andIntro ⟨symm hr⟩ ⟨symm hold⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalListReturnContentProof

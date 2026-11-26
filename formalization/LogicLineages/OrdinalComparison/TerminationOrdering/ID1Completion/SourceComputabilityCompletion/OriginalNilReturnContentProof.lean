module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNilReturnContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnStackContentSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNilReturnContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel z zRelabel)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualNilContent : OriginalNilReturnContentTargets.NilContent := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out outRest outOld value
  hstate hwork hframe hrole hraw htag hchildren hcount hlength hreverse happend hactual hout hstack
 let s : Program 2 := consOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
 let o : Program 2 := pairOf (.projection 1) s
 let qs : Fin 2 → Program 2 := ![s,o]
 let xs : Fin 2 → OTerm alpha := ![old,rest]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![old.relabel j,rest.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
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
 have hactual' := renameInto hactual j Theta hinc
 have hout' := renameInto hout j Theta hinc
 have hstack' := renameInto hstack j Theta hinc
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,zRelabel] at hstate' hwork' hframe' hrole' hraw' htag' hchildren' hcount' hlength' hreverse' happend' hactual' hout' hstack'
 have hs := binaryRecover InternalListCodec.consCode (OriginalRawSyntaxTransport.constant 2 0) (.projection 0) (ys 0) z (old.relabel j) xx
  (hq 0) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx) (projectionValue 0 xx)
 have ho := binaryRecover InternalPairing.pairing (.projection 1) s (ys 1) (rest.relabel j) (ys 0) xx (hq 1) (projectionValue 1 xx) (hq 0)
 have hforward := OriginalRestoredListReturnProof.listNil R body beta Theta
  (input.relabel j) (work.relabel j) (results.relabel j) (frame.relabel j) (rest.relabel j) (payload.relabel j)
  (raw.relabel j) (rawPayload.relabel j) (count.relabel j) (row.relabel j) (reversed.relabel j) (old.relabel j) (ys 0) (ys 1)
  hstate' hwork' hframe' hrole' hraw' htag' hchildren' hcount' hlength' hreverse' happend' hs ho
 have restored := OriginalReturnStackContentSupportProof.restoreFields (OriginalHereditaryReturnStep.step R)
  (input.relabel j) (ys 1) (out.relabel j) (rest.relabel j) (outRest.relabel j) (ys 0) (stack.relabel j)
  z (value.relabel j) (old.relabel j) (outOld.relabel j) hforward hactual' ho hs hout' hstack'
 obtain ⟨hv⟩ := andLeft restored
 obtain ⟨hr⟩ := andLeft (andRight restored)
 obtain ⟨hold⟩ := andRight (andRight restored)
 simp only [conjunctionRename,eqnRelabel,zRelabel]
 exact andIntro ⟨symm hv⟩ (andIntro ⟨symm hr⟩ ⟨symm hold⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNilReturnContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNilReturnContentProof

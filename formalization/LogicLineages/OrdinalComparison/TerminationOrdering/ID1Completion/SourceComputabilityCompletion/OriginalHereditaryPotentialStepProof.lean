module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqnRelabel zRelabel)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open OriginalTypedDecoderInternalAcceptanceUnaryProof (notRename)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All concrete runtime and potential effects are discharged. Only the actual
agenda visit-preservation endpoint remains an explicit staging supplier. -/
theorem fromVisitPreservation (visitPres : OriginalHereditaryInternalAgendaTargets.VisitPreservation)
 (R : Program 2) (H : Program 1) (M W : Program 2) : OriginalHereditaryPotentialCompletion.StepLaw R H M W := by
 intro body alpha Delta c B input work results before next nextWork nextResults after hs ha hb hnon hn hp hm
 let qs : Fin 2 → Program 1 := ![InternalListCodec.headCode,InternalListCodec.tailCode]
 let xs : Fin 1 → OTerm alpha := Fin.cons work Fin.elim0
 apply queryCases qs xs _
 intro beta j ys Theta hinc hq
 simp only [conjunctionRename,agendaRename,orderRename]
 let xx : Fin 1 → OTerm beta := Fin.cons (work.relabel j) Fin.elim0
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hs' := renameInto hs j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hnon' := renameInto hnon j Theta hinc
 have hn' := renameInto hn j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hm' := renameInto hm j Theta hinc
 simp only [graph1Rename,graph2Rename,agendaRename,notRename,eqnRelabel,zRelabel] at hs' ha' hb' hnon' hn' hp' hm'
 have hc := InternalListCodecDecompositionSupportProof.reconstructNonzero (work.relabel j) (ys 0) (ys 1) hnon' (hq 0) (hq 1)
 have hf := OriginalHereditaryInternalAgendaStructuralProof.head H M W (c.relabel j) (B.relabel j) (work.relabel j) (ys 0) (ys 1) ha' hc
 exact OriginalHereditaryPotentialStepFrameProof.atFrame visitPres R H M W
   (c.relabel j) (B.relabel j) (input.relabel j) (work.relabel j) (results.relabel j) (before.relabel j)
   (next.relabel j) (nextWork.relabel j) (nextResults.relabel j) (after.relabel j) (ys 0) (ys 1)
   hs' ha' hb' hn' hp' hm' hc hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialStepProof

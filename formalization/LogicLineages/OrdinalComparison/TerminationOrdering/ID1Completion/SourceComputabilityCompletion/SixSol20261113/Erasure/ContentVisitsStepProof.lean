module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsAllProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionAllProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime ContentVisitsDefinitions ContentVisitsSyntax ContentVisitsInductionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withHead (R : Program 2) (size jobs head tail tagged forward produced headCount value : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R size)))
 (hf : Nonempty (Derivation body Delta (fields R (suc size) jobs tagged forward produced)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs head tail)))
 (hh : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R head headCount value))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 have hl := OriginalContextInsertionSupportProof.successorLengthTail jobs head tail size hc (andLeft hf)
 have hallComplete := andLeft (andRight (andRight hf))
 have hallContent := andLeft (andRight (andRight (andRight hf)))
 have htComplete := VisitListCompletionAllProof.tailComplete R size jobs head tail hallComplete hc
 have htContent := ContentVisitsAllProof.tailContent R size jobs head tail hallContent hc
 have hhead := FramedContentSyntax.contentApply R head headCount value
   (ContentVisitsAllProof.headContent R size jobs head tail hallContent hc) hh
 let tp : Program 2 := .composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => .projection 1)
 let vp : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
 let mp : Program 2 := .composition (InternalListMap.map (k := 0) (FramedContentDefinitions.contentProgram R))
   (fun _ : Fin 1 => .projection 1)
 let rp : Program 2 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => mp)
 let qs : Fin 4 → Program 2 := ![tp,vp,mp,rp]
 let xs : Fin 2 → OTerm alpha := ![head,tail]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![head.relabel j,tail.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hh' := renameInto hh j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have htComplete' := renameInto htComplete j Theta hinc
 have htContent' := renameInto htContent j Theta hinc
 have hhead' := renameInto hhead j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel,graph2Rename,OriginalContextInsertionSyntaxProof.lengthRename,
   VisitListCompletionSyntax.allRename,allRename,JobFrameSyntax.frameRename,
   FramedContentDefinitions.Content,graph1Rename] at hi' hf' hc' hh' hl' htComplete' htContent' hhead'
 have htagTail := unaryRecover OriginalHereditaryVisitScheduler.tagVisits (.projection 1)
   (ys 0) (tail.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hframe := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
   (ys 1) z (head.relabel j) xx (hq 1)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx) (projectionValue 0 xx)
 have hmapTail := unaryRecover (InternalListMap.map (k := 0) (FramedContentDefinitions.contentProgram R))
   (.projection 1) (ys 2) (tail.relabel j) xx (hq 2) (projectionValue 1 xx)
 have hreverseTail := unaryRecover OriginalTypedArgumentObservations.reverse mp
   (ys 3) (ys 2) xx (hq 3) (hq 2)
 have htagCons := OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagCons
   (jobs.relabel j) (head.relabel j) (tail.relabel j) (tagged.relabel j) (ys 1) (ys 0)
   hc' hframe htagTail (andLeft (andRight hf'))
 have hforward := InternalListMapProof.consForward (FramedContentDefinitions.contentProgram R)
   (jobs.relabel j) (head.relabel j) (tail.relabel j) (value.relabel j) (ys 2) (forward.relabel j)
   Fin.elim0 hc' hhead' hmapTail (andLeft (andRight (andRight (andRight (andRight hf')))))
 have htail := rowApply R (size.relabel j) (tail.relabel j) (ys 0) (ys 2) (ys 3) hi'
   (andIntro hl' (andIntro htagTail (andIntro htComplete' (andIntro htContent' (andIntro hmapTail hreverseTail)))))
 rw [countedRename]
 exact ContentVisitsConsQueries.assemble R (head.relabel j) (ys 1) (tagged.relabel j) (ys 0)
   (headCount.relabel j) (value.relabel j) (ys 3) (forward.relabel j) (ys 2) (produced.relabel j)
   hh' htail hframe htagCons hforward hreverseTail (andRight (andRight (andRight (andRight (andRight hf')))))

theorem consCore (R : Program 2) (size jobs head tail tagged forward produced : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R size)))
 (hf : Nonempty (Derivation body Delta (fields R (suc size) jobs tagged forward produced)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode jobs head tail))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 have hh := VisitListCompletionAllProof.headComplete R size jobs head tail (andLeft (andRight (andRight hf))) hc
 apply JobCompletionSyntax.completionCases R head _ hh
 intro beta j Theta count value hinc hframe
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel,graph2Rename] at hi' hf' hc'
 rw [countedRename]
 exact withHead R (size.relabel j) (jobs.relabel j) (head.relabel j) (tail.relabel j)
   (tagged.relabel j) (forward.relabel j) (produced.relabel j) count value hi' hf' hc' hframe

theorem successorCore (R : Program 2) (size jobs tagged forward produced : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R size)))
 (hf : Nonempty (Derivation body Delta (fields R (suc size) jobs tagged forward produced))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 apply OriginalContextInsertionLengthProof.nonzeroCases jobs _
   (OriginalContextInsertionSupportProof.successorLengthNonzero size jobs (andLeft hf))
 intro beta j Theta head tail hinc hc
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [rowRename,fieldsRename,sucRelabel] at hi' hf'
 rw [countedRename]
 exact consCore R (size.relabel j) (jobs.relabel j) head tail (tagged.relabel j)
   (forward.relabel j) (produced.relabel j) hi' hf' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStepProof

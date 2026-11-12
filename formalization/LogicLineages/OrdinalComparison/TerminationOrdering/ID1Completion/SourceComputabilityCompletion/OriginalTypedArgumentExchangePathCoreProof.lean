module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalTypedArgumentExchangePath OriginalTypedArgumentExchangePathInductionDefinitions OriginalTypedArgumentExchangePathSyntaxProof OriginalTypedArgumentExchangePathBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {R : Program 2} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] mapPath entryMap OriginalTypedArgumentObservations.argumentObservations

theorem entryValue (entry vertex certificate parameter observed numeric mapped : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry vertex certificate)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observed vertex parameter)))
 (hn : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentExchange.translate R) numeric certificate parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mapped observed numeric))) :
 Nonempty (Derivation body Delta (graph2 (entryMap R) mapped entry parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons entry (Fin.cons parameter Fin.elim0)
 have hl := unaryValue InternalUnpair.left (.projection 0) vertex entry xs (pairLeft _ _ _ hp) (projectionValue 0 xs)
 have hr := unaryValue InternalUnpair.right (.projection 0) certificate entry xs (pairRight _ _ _ hp) (projectionValue 0 xs)
 have ho := binaryValue (OriginalTypedArgumentObservations.argumentObservations R) (leftOf (.projection 0)) (.projection 1)
   observed vertex parameter xs hv hl (projectionValue 1 xs)
 have hc := binaryValue (OriginalTypedArgumentExchange.translate R) (rightOf (.projection 0)) (.projection 1)
   numeric certificate parameter xs hn hr (projectionValue 1 xs)
 simpa only [entryMap,pairOf] using binaryValue InternalPairing.pairing (observedVertex R) (numericCertificate R)
   mapped observed numeric xs hm ho hc

theorem atZero (raw source target parameter observedSource observedTarget mapped : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields R raw source target parameter observedSource observedTarget mapped))) :
 Nonempty (Derivation body Delta (result observedSource observedTarget mapped)) := by
 have hp : Nonempty (Derivation body Delta (InternalPathChecker.pathGraph OriginalTypedArgumentExchange.edge source target z)) := by
   apply graphInputTransport body alpha 3 Delta _ (suc z)
     (Fin.cons source (Fin.cons target (Fin.cons raw Fin.elim0)))
     (Fin.cons source (Fin.cons target (Fin.cons z Fin.elim0))) _ (andLeft hf)
   intro i
   refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
   · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl source⟩
   · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl target⟩
   · rw [onEquality]; exact hz
 obtain ⟨he⟩ := InternalPathCheckerProof.nilRecover OriginalTypedArgumentExchange.edge source target hp
 have hs := headTransport (OriginalTypedArgumentObservations.argumentObservations R) observedSource source target (Fin.cons parameter Fin.elim0)
   (by simpa only [equalEqn] using (Nonempty.intro he)) (andLeft (andRight hf))
 have heNew := valueUnique (OriginalTypedArgumentObservations.argumentObservations R) observedSource observedTarget
   (Fin.cons target (Fin.cons parameter Fin.elim0)) hs (andLeft (andRight (andRight hf)))
 have hm := headTransport (mapPath R) mapped raw z (Fin.cons parameter Fin.elim0) hz (andRight (andRight (andRight hf)))
 have hmView : Nonempty (Derivation body Delta (programGraph (InternalListMap.map (entryMap R)) mapped (Fin.cons z (Fin.cons parameter Fin.elim0)))) := by
   simpa only [mapPath,graph2] using hm
 obtain ⟨hmEq⟩ := InternalListMapProof.actualOriginalListMapZero body 1 (entryMap R) alpha mapped (Fin.cons parameter Fin.elim0)
 obtain ⟨hmz⟩ := InternalRecursionClosureLogicProof.closedApply ⟨Derivation.conjunctionLeft hmEq⟩ hmView
 have hnil := iffBackward (InternalPathCheckerProof.pathNil OriginalNumericListSortExchange.edge observedSource observedTarget)
   (by simpa only [equalEqn] using heNew)
 exact OriginalNumericListSortExchangePathPrependCoreProof.rawTransport observedSource observedTarget z mapped
   ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using hmz)⟩ hnil

theorem atCons (raw source target parameter observedSource observedTarget mapped entry rest : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw R raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw entry rest)))
 (hf : Nonempty (Derivation body Delta (fields R raw source target parameter observedSource observedTarget mapped))) :
 Nonempty (Derivation body Delta (result observedSource observedTarget mapped)) := by
 apply OriginalTypedArgumentObservationsWalkQueryProof.pairCases entry _
 intro beta j Theta vertex certificate hj hp
 rw [resultRename]
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fields,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,
   conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
 let q0 : Program 4 := .composition (OriginalTypedArgumentObservations.argumentObservations R) ![.projection 0,.projection 3]
 let q1 : Program 4 := .composition (OriginalTypedArgumentExchange.translate R) ![.projection 1,.projection 3]
 let q2 : Program 4 := .composition (mapPath R) ![.projection 2,.projection 3]
 let qs : Fin 4 → Program 4 := ![q0,q1,q2,pairOf q0 q1]
 let xs : Fin 4 → OTerm beta := Fin.cons vertex (Fin.cons certificate (Fin.cons (rest.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro gamma l w Xi hl hq
 rw [resultRename]
 have hvec : (fun i : Fin 4 => (xs i).relabel l) =
   Fin.cons (vertex.relabel l) (Fin.cons (certificate.relabel l) (Fin.cons ((rest.relabel j).relabel l) (Fin.cons ((parameter.relabel j).relabel l) Fin.elim0))) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 let ys : Fin 4 → OTerm gamma := Fin.cons (vertex.relabel l) (Fin.cons (certificate.relabel l) (Fin.cons ((rest.relabel j).relabel l) (Fin.cons ((parameter.relabel j).relabel l) Fin.elim0)))
 have hq' (i : Fin 4) : Nonempty (Derivation body Xi (programGraph (qs i) (w i) ys)) := by
   simpa only [hvec,ys] using hq i
 have h0 : Nonempty (Derivation body Xi (programGraph (q0) (w 0) ys)) := by
   have hselect : qs (0 : Fin 4) = q0 := rfl
   simpa only [hselect] using hq' 0
 have h1 : Nonempty (Derivation body Xi (programGraph (q1) (w 1) ys)) := by
   have hselect : qs (1 : Fin 4) = q1 := rfl
   simpa only [hselect] using hq' 1
 have h2 : Nonempty (Derivation body Xi (programGraph (q2) (w 2) ys)) := by
   have hselect : qs (2 : Fin 4) = q2 := rfl
   simpa only [hselect] using hq' 2
 have h3 : Nonempty (Derivation body Xi (programGraph (pairOf q0 q1) (w 3) ys)) := by
   have hselect : qs (3 : Fin 4) = pairOf q0 q1 := rfl
   simpa only [hselect] using hq' 3

 have hov := binaryRecover (OriginalTypedArgumentObservations.argumentObservations R) (.projection 0) (.projection 3)
   (w 0) (vertex.relabel l) ((parameter.relabel j).relabel l) ys h0 (projectionValue 0 ys) (projectionValue 3 ys)
 have hnc := binaryRecover (OriginalTypedArgumentExchange.translate R) (.projection 1) (.projection 3)
   (w 1) (certificate.relabel l) ((parameter.relabel j).relabel l) ys h1 (projectionValue 1 ys) (projectionValue 3 ys)
 have hmr := binaryRecover (mapPath R) (.projection 2) (.projection 3)
   (w 2) ((rest.relabel j).relabel l) ((parameter.relabel j).relabel l) ys h2 (projectionValue 2 ys) (projectionValue 3 ys)
 have hpair := binaryRecover InternalPairing.pairing q0 q1 (w 3) (w 0) (w 1) ys h3 h0 h1
 have hi'' := renameInto hi' l Xi hl
 rw [belowRawRename] at hi''
 have hc'' := renameInto hc' l Xi hl
 have hp' := renameInto hp l Xi hl
 rw [graph2Rename] at hc'' hp'
 have hf'' := renameInto hf' l Xi hl
 simp only [conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf''
 have oldParts := iffForward (InternalPathCheckerProof.pathCons OriginalTypedArgumentExchange.edge
   ((source.relabel j).relabel l) ((target.relabel j).relabel l) ((raw.relabel j).relabel l)
   ((entry.relabel j).relabel l) ((rest.relabel j).relabel l) (vertex.relabel l) (certificate.relabel l) hp' hc'') (andLeft hf'')
 have newEdge := OriginalTypedArgumentExchangeProof.actualTranslation R body gamma Xi
   ((source.relabel j).relabel l) (vertex.relabel l) (certificate.relabel l) ((parameter.relabel j).relabel l)
   ((observedSource.relabel j).relabel l) (w 0) (w 1) (andLeft oldParts) (andLeft (andRight hf'')) hov hnc
 have newTail := belowRawApply ((raw.relabel j).relabel l) ((rest.relabel j).relabel l) (vertex.relabel l)
   ((target.relabel j).relabel l) ((parameter.relabel j).relabel l) (w 0) ((observedTarget.relabel j).relabel l) (w 2) hi''
   (InternalListCodecDecompositionSupportProof.consTailDescent ((raw.relabel j).relabel l) ((entry.relabel j).relabel l) ((rest.relabel j).relabel l) hc'')
   (andIntro (andRight oldParts) (andIntro hov (andIntro (andLeft (andRight (andRight hf''))) hmr)))
 have hentry := entryValue ((entry.relabel j).relabel l) (vertex.relabel l) (certificate.relabel l) ((parameter.relabel j).relabel l)
   (w 0) (w 1) (w 3) hp' hov hnc hpair
 have hmView : Nonempty (Derivation body Xi (graph2 (InternalListMap.map (entryMap R)) ((mapped.relabel j).relabel l)
   ((raw.relabel j).relabel l) ((parameter.relabel j).relabel l))) := by
   simpa only [mapPath] using andRight (andRight (andRight hf''))
 have hrView : Nonempty (Derivation body Xi (graph2 (InternalListMap.map (entryMap R)) (w 2)
   ((rest.relabel j).relabel l) ((parameter.relabel j).relabel l))) := by simpa only [mapPath] using hmr
 have hnewcons := InternalListMapProof.consForward (entryMap R) ((raw.relabel j).relabel l) ((entry.relabel j).relabel l)
   ((rest.relabel j).relabel l) (w 3) (w 2) ((mapped.relabel j).relabel l) (Fin.cons ((parameter.relabel j).relabel l) Fin.elim0)
   hc'' hentry hrView hmView
 exact iffBackward (InternalPathCheckerProof.pathCons OriginalNumericListSortExchange.edge
   ((observedSource.relabel j).relabel l) ((observedTarget.relabel j).relabel l) ((mapped.relabel j).relabel l)
   (w 3) (w 2) (w 0) (w 1) hpair hnewcons) (andIntro newEdge newTail)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathCoreProof

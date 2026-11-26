module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalNumericListSortExchange (edge)
open OriginalNumericListSortExchangePathPrefix OriginalNumericListSortExchangePathPrefixInductionDefinitions OriginalNumericListSortExchangePathPrefixSyntaxProof OriginalNumericListSortExchangePathPrefixBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] mapPrefix edge

theorem atZero (raw source target path newSource newTarget mapped : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw source target path newSource newTarget mapped))) :
 Nonempty (Derivation body Delta (result newSource newTarget mapped)) := by
 have hs := headTransport InternalApplicationValidityStackAppend.append newSource raw z (Fin.cons source Fin.elim0) hz (andLeft (andRight hf))
 have ht := headTransport InternalApplicationValidityStackAppend.append newTarget raw z (Fin.cons target Fin.elim0) hz (andLeft (andRight (andRight hf)))
 obtain ⟨hes⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover newSource source hs
 obtain ⟨het⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover newTarget target ht
 have hm := headTransport mapPrefix mapped raw z (Fin.cons path Fin.elim0) hz (andRight (andRight (andRight hf)))
 obtain ⟨hem⟩ := valueUnique mapPrefix mapped path (Fin.cons z (Fin.cons path Fin.elim0)) hm (OriginalNumericListSortExchangePathPrefixRecursionProof.atZero path)
 apply graphInputTransport body alpha 3 Delta _ (suc z)
   (Fin.cons source (Fin.cons target (Fin.cons path Fin.elim0)))
   (Fin.cons newSource (Fin.cons newTarget (Fin.cons mapped Fin.elim0))) _ (andLeft hf)
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.symm hes⟩
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.symm het⟩
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.symm hem⟩

theorem atCons (raw source target path newSource newTarget mapped head rest : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head rest)))
 (hf : Nonempty (Derivation body Delta (fields raw source target path newSource newTarget mapped))) :
 Nonempty (Derivation body Delta (result newSource newTarget mapped)) := by
 let qs : Fin 3 → Program 4 := ![
   .composition InternalApplicationValidityStackAppend.append ![.projection 0,.projection 1],
   .composition InternalApplicationValidityStackAppend.append ![.projection 0,.projection 2],
   .composition mapPrefix ![.projection 0,.projection 3] ]
 let xs : Fin 4 → OTerm alpha := Fin.cons rest (Fin.cons source (Fin.cons target (Fin.cons path Fin.elim0)))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j vals Theta hj hq
 rw [resultRename]
 have hv : (fun i : Fin 4 => (xs i).relabel j) =
   Fin.cons (rest.relabel j) (Fin.cons (source.relabel j) (Fin.cons (target.relabel j) (Fin.cons (path.relabel j) Fin.elim0))) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 let ys : Fin 4 → OTerm beta := Fin.cons (rest.relabel j) (Fin.cons (source.relabel j) (Fin.cons (target.relabel j) (Fin.cons (path.relabel j) Fin.elim0)))
 have hq' (i : Fin 3) : Nonempty (Derivation body Theta (programGraph (qs i) (vals i) ys)) := by
   simpa only [hv,ys] using hq i
 have hs : Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append (vals 0) (rest.relabel j) (source.relabel j))) := by
   apply binaryRecover InternalApplicationValidityStackAppend.append (.projection 0) (.projection 1) (vals 0) (rest.relabel j) (source.relabel j) ys _ (projectionValue 0 ys) (projectionValue 1 ys)
   exact hq' 0
 have ht : Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append (vals 1) (rest.relabel j) (target.relabel j))) := by
   apply binaryRecover InternalApplicationValidityStackAppend.append (.projection 0) (.projection 2) (vals 1) (rest.relabel j) (target.relabel j) ys _ (projectionValue 0 ys) (projectionValue 2 ys)
   have hselect : qs (1 : Fin 3) = .composition InternalApplicationValidityStackAppend.append ![.projection 0,.projection 2] := rfl
   simpa only [hselect] using hq' 1
 have hm : Nonempty (Derivation body Theta (graph2 mapPrefix (vals 2) (rest.relabel j) (path.relabel j))) := by
   apply binaryRecover mapPrefix (.projection 0) (.projection 3) (vals 2) (rest.relabel j) (path.relabel j) ys _ (projectionValue 0 ys) (projectionValue 3 ys)
   have hselect : qs (2 : Fin 3) = .composition mapPrefix ![.projection 0,.projection 3] := rfl
   simpa only [hselect] using hq' 2
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fields,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,
   conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
 have htail := belowRawApply (raw.relabel j) (rest.relabel j) (source.relabel j) (target.relabel j)
   (path.relabel j) (vals 0) (vals 1) (vals 2) hi'
   (InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (head.relabel j) (rest.relabel j) hc')
   (andIntro (andLeft hf') (andIntro hs (andIntro ht hm)))
 have hsource := InternalApplicationValidityStackAppendListProof.consForward (raw.relabel j) (head.relabel j) (rest.relabel j)
   (source.relabel j) (vals 0) (newSource.relabel j) hc' hs (andLeft (andRight hf'))
 have htarget := InternalApplicationValidityStackAppendListProof.consForward (raw.relabel j) (head.relabel j) (rest.relabel j)
   (target.relabel j) (vals 1) (newTarget.relabel j) hc' ht (andLeft (andRight (andRight hf')))
 have hmap := OriginalNumericListSortExchangePathPrefixRecursionProof.consForward (raw.relabel j) (head.relabel j) (rest.relabel j)
   (path.relabel j) (vals 2) (mapped.relabel j) hc' hm (andRight (andRight (andRight hf')))
 exact OriginalNumericListSortExchangePathPrependProof.actualPathPrepend body beta Theta
   (vals 2) (vals 0) (vals 1) (head.relabel j) (newSource.relabel j) (newTarget.relabel j) (mapped.relabel j)
   htail hsource htarget hmap
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixCoreProof

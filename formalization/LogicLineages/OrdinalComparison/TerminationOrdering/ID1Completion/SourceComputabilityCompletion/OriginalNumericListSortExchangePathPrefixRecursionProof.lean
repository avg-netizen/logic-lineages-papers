module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependRecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixRecursionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRawListRecursion InternalRawListRecursionProof InternalRawListRecursionSyntaxProof
open InternalRecursionClosureLogicProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalNumericListSortExchangePathPrefix
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] mapPrefix OriginalNumericListSortExchangePathPrepend.mapPath

theorem atZero (path : OTerm alpha) :
 Nonempty (Derivation body Delta (graph2 mapPrefix path z path)) := by
 obtain ⟨he⟩ := actualOriginalListRecursionZero body 1 (.projection 0) step alpha path (Fin.cons path Fin.elim0)
 have hv : Nonempty (Derivation body Delta (recGraph (.projection 0) step path z (Fin.cons path Fin.elim0))) :=
   closedApply ⟨Derivation.conjunctionRight he⟩ (projectionValue 0 (Fin.cons path Fin.elim0))
 simpa only [mapPrefix,graph2,recGraph] using hv

theorem consBackward (raw head rest path tailMapped out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head rest)))
 (hr : Nonempty (Derivation body Delta (graph2 mapPrefix tailMapped rest path)))
 (ho : Nonempty (Derivation body Delta (graph2 OriginalNumericListSortExchangePathPrepend.mapPath out tailMapped head))) :
 Nonempty (Derivation body Delta (graph2 mapPrefix out raw path)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons head (Fin.cons tailMapped (Fin.cons path Fin.elim0))
 have hs : Nonempty (Derivation body Delta (graph3 step out head tailMapped path)) :=
   binaryValue OriginalNumericListSortExchangePathPrepend.mapPath (.projection 1) (.projection 0) out tailMapped head xs ho
     (projectionValue 1 xs) (projectionValue 0 xs)
 have hrView : Nonempty (Derivation body Delta (recGraph (.projection 0) step tailMapped rest (Fin.cons path Fin.elim0))) := by
   simpa only [mapPrefix,graph2,recGraph] using hr
 obtain ⟨hr⟩ := hrView
 obtain ⟨hs⟩ := hs
 have hex : Nonempty (Derivation body Delta (consStep (.projection 0) step out head rest (Fin.cons path Fin.elim0))) := by
   apply Nonempty.intro
   apply Derivation.existentialIntroduction (emb tailMapped)
   rw [consStepInstance]
   exact Derivation.conjunctionIntroduction hr hs
 obtain ⟨heq⟩ := closedApply (actualOriginalListRecursionCons body 1 (.projection 0) step
   alpha raw head rest out (Fin.cons path Fin.elim0)) hc
 obtain ⟨hex⟩ := hex
 have hv : Nonempty (Derivation body Delta (recGraph (.projection 0) step out raw (Fin.cons path Fin.elim0))) :=
   ⟨Derivation.implicationElimination (Derivation.conjunctionRight heq) hex⟩
 simpa only [mapPrefix,graph2,recGraph] using hv

theorem consForward (raw head rest path tailMapped out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head rest)))
 (hr : Nonempty (Derivation body Delta (graph2 mapPrefix tailMapped rest path)))
 (ho : Nonempty (Derivation body Delta (graph2 mapPrefix out raw path))) :
 Nonempty (Derivation body Delta (graph2 OriginalNumericListSortExchangePathPrepend.mapPath out tailMapped head)) := by
 apply OriginalTypedArgumentObservationsAccumulatorQueryProof.binaryCases OriginalNumericListSortExchangePathPrepend.mapPath tailMapped head _
 intro beta j Theta result hj hresult
 rw [graph2Rename]
 have hc' := renameInto hc j Theta hj
 have hr' := renameInto hr j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [graph2Rename] at hc' hr' ho'
 have hm := consBackward (raw.relabel j) (head.relabel j) (rest.relabel j) (path.relabel j)
   (tailMapped.relabel j) result hc' hr' hresult
 exact outputTransport OriginalNumericListSortExchangePathPrepend.mapPath result (out.relabel j)
   (Fin.cons (tailMapped.relabel j) (Fin.cons (head.relabel j) Fin.elim0))
   (valueUnique mapPrefix result (out.relabel j) (Fin.cons (raw.relabel j) (Fin.cons (path.relabel j) Fin.elim0)) hm ho') hresult
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixRecursionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixRecursionProof

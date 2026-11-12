module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalNumericListSort OriginalNumericListSortExchange
open OriginalNumericListSortExchangePathDefinitions OriginalNumericListSortExchangePathSyntaxProof
open OriginalNumericListSortExchangePathBindingProof OriginalNumericListSortAdjacentSupportProof
open OriginalTypedArgumentObservationsWalkQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] sort edge

theorem atZero (raw source target left right : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw source target left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hp : Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target z)) := by
   apply graphInputTransport body alpha 3 Delta _ (suc z)
     (Fin.cons source (Fin.cons target (Fin.cons raw Fin.elim0)))
     (Fin.cons source (Fin.cons target (Fin.cons z Fin.elim0))) _ (andLeft hf)
   intro i
   refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
   · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl source⟩
   · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl target⟩
   · rw [onEquality]; exact hz
 obtain ⟨he⟩ := InternalPathCheckerProof.nilRecover edge source target hp
 have hs := headTransport sort left source target Fin.elim0
   (by simpa only [equalEqn] using (Nonempty.intro he)) (andLeft (andRight hf))
 simpa only [equalEqn] using valueUnique sort left right (Fin.cons target Fin.elim0) hs (andRight (andRight hf))

theorem atCons (raw source target left right entry rest : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw entry rest)))
 (hf : Nonempty (Derivation body Delta (fields raw source target left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply pairCases entry _
 intro beta j Theta vertex certificate hj hp
 rw [equalRename]
 have hi' := renameInto hi j Theta hj
 have hc' := renameInto hc j Theta hj
 have hf' := renameInto hf j Theta hj
 rw [belowRawRename] at hi'
 rw [graph2Rename] at hc'
 simp only [fields,SourceComputabilityFormulaSupportProof.numeral,conjunctionRename,graph1Rename,graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
 apply unaryCases sort vertex _
 intro gamma k Xi middle hk hm
 rw [equalRename]
 have hi'' := renameInto hi' k Xi hk
 have hc'' := renameInto hc' k Xi hk
 have hf'' := renameInto hf' k Xi hk
 have hp' := renameInto hp k Xi hk
 rw [belowRawRename] at hi''
 rw [graph2Rename] at hc'' hp'
 simp only [conjunctionRename,graph1Rename,graph3Rename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf''
 have hparts := iffForward (InternalPathCheckerProof.pathCons edge
   ((source.relabel j).relabel k) ((target.relabel j).relabel k) ((raw.relabel j).relabel k)
   ((entry.relabel j).relabel k) ((rest.relabel j).relabel k) (vertex.relabel k) (certificate.relabel k) hp' hc'') (andLeft hf'')
 have hleft := OriginalNumericListSortExchangeProof.acceptedAt ((source.relabel j).relabel k)
   (vertex.relabel k) (certificate.relabel k) ((left.relabel j).relabel k) middle
   (andLeft hparts) (andLeft (andRight hf'')) hm
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent
   ((raw.relabel j).relabel k) ((entry.relabel j).relabel k) ((rest.relabel j).relabel k) hc''
 have hright := belowRawApply ((raw.relabel j).relabel k) ((rest.relabel j).relabel k)
   (vertex.relabel k) ((target.relabel j).relabel k) middle ((right.relabel j).relabel k) hi'' hb
   (andIntro (andRight hparts) (andIntro hm (andRight (andRight hf''))))
 obtain ⟨hleft⟩ := hleft
 obtain ⟨hright⟩ := hright
 simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.trans
   (by simpa only [equalEqn] using hleft) (by simpa only [equalEqn] using hright)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathCoreProof

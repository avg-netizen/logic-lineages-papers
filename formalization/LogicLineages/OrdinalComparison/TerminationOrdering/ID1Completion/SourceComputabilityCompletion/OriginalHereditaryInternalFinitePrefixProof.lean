module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsAppendProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem boundedCons : OriginalHereditaryInternalFinitePrefixTargets.BoundedCons := by
 intro body alpha Delta row head tail count index value psi hc hl hb hv zero next
 apply zeroSuccessorCases Delta index psi
 · let Theta := eqn index z :: Delta
   have inc : ∀ f ∈ Delta, f ∈ Theta := fun f hf => List.mem_cons_of_mem _ hf
   have he : Nonempty (Derivation body Theta (eqn index z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hlookup := headTransport InternalRawListRecursion.lookup value index z (Fin.cons row Fin.elim0) he (weakenProof hv inc)
   have hhead := OriginalAllPositionContextDeleteBaseProof.lookupZero row head tail (weakenProof hc inc)
   exact zero Theta inc (valueUnique InternalRawListRecursion.lookup value head (Fin.cons z (Fin.cons row Fin.elim0)) hlookup hhead)
 · intro beta j Theta pred hj he
   have hc' := renameInto hc j Theta hj
   rw [consGraphRename] at hc'
   have hl' := renameInto hl j Theta hj
   rw [lengthRename] at hl'
   have hb' := renameInto hb j Theta hj
   simp only [Below,orderRename] at hb'
   have hv' := renameInto hv j Theta hj
   rw [graph2Rename] at hv'
   apply programCases length (Fin.cons (tail.relabel j) Fin.elim0) _
   intro gamma k Xi tailCount hk htail
   simp only [consTermRename,emptyRename] at htail
   change Nonempty (Derivation body Xi (lengthGraph tailCount ((tail.relabel j).relabel k))) at htail
   have hc'' := renameInto hc' k Xi hk
   rw [consGraphRename] at hc''
   have hl'' := renameInto hl' k Xi hk
   rw [lengthRename] at hl''
   have hb'' := renameInto hb' k Xi hk
   rw [orderRename] at hb''
   have hv'' := renameInto hv' k Xi hk
   rw [graph2Rename] at hv''
   have he' := renameInto he k Xi hk
   simp only [eqnRename,sucRelabel] at he'
   obtain ⟨hlen⟩ := lengthConsRecover ((row.relabel j).relabel k) ((head.relabel j).relabel k)
     ((tail.relabel j).relabel k) ((count.relabel j).relabel k) tailCount hc'' hl'' htail
   obtain ⟨heq⟩ := he'
   obtain ⟨hbv⟩ := hb''
   have hbound := OriginalContextInsertionBelowCoreProof.successorStrict (pred.relabel k) tailCount
     ⟨orderRight (suc (pred.relabel k)) hlen (orderLeft ((count.relabel j).relabel k) heq hbv)⟩
   have hlookup := headTransport InternalRawListRecursion.lookup ((value.relabel j).relabel k)
     ((index.relabel j).relabel k) (suc (pred.relabel k)) (Fin.cons ((row.relabel j).relabel k) Fin.elim0) ⟨heq⟩ hv''
   obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff
     ((row.relabel j).relabel k) ((head.relabel j).relabel k) ((tail.relabel j).relabel k)
     (pred.relabel k) ((value.relabel j).relabel k) hc''
   obtain ⟨hlookup⟩ := hlookup
   have hlookupTail := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft hiff) hlookup)
   have result := next gamma (k ∘ j) Xi (pred.relabel k) tailCount
     (by intro f hf; simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk _ (hj f hf))
     (by simpa only [Term.relabel_relabel] using htail) hbound
     (by simpa only [Term.relabel_relabel] using hlookupTail)
   simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using result
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof

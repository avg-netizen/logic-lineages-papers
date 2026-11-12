module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupLiftProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftSuccessor)
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalSquareRootArithmeticSupportProof (orderLeft)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalInternalAppendLookup OriginalInternalAppendLookupSyntaxProof OriginalInternalAppendLookupBindingProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalQuotientComparisonProof (orLeft orRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem firstAt (count front head tail suffix index value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
 (hi : Nonempty (Derivation body Delta (eqn index z)))
 (hv : Nonempty (Derivation body Delta (eqn value head))) :
 Nonempty (Derivation body Delta (Result (suc count) front suffix index value)) := by
 have hzero := OriginalAllPositionContextDeleteBaseProof.lookupZero front head tail hc
 obtain ⟨hv⟩ := hv
 obtain ⟨hi⟩ := hi
 have hvalue := outputTransport InternalRawListRecursion.lookup head value
   (Fin.cons z (Fin.cons front Fin.elim0)) ⟨symm hv⟩ hzero
 have hlookup := headTransport InternalRawListRecursion.lookup value z index (Fin.cons front Fin.elim0) ⟨symm hi⟩ hvalue
 obtain ⟨hb⟩ := OriginalHereditaryBudgetSumBoundCellsProof.zeroBound (body := body) (Delta := Delta) count
 have hbound := Nonempty.intro (orderLeft (suc count) (symm hi) hb)
 obtain ⟨h⟩ := InternalApplicationStepPeelSupportProof.andIntro hbound hlookup
 exact ⟨orLeft h⟩

theorem liftResult (count front head tail suffix index pred value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
 (hi : Nonempty (Derivation body Delta (eqn index (suc pred))))
 (hr : Nonempty (Derivation body Delta (Result count tail suffix pred value))) :
 Nonempty (Derivation body Delta (Result (suc count) front suffix index value)) := by
 apply orCases hr
 · intro Theta inc hh
   have hc' := weakenProof hc inc
   obtain ⟨hi'⟩ := weakenProof hi inc
   obtain ⟨hb⟩ := InternalRecursionGraphExtensionSupportProof.successorOrder pred count
     (InternalApplicationStepPeelSupportProof.andLeft hh)
   have hbound := Nonempty.intro (orderLeft (suc count) (symm hi') hb)
   obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff front head tail pred value hc'
   obtain ⟨ht⟩ := InternalApplicationStepPeelSupportProof.andRight hh
   have hs := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight hiff) ht)
   have hlookup := headTransport InternalRawListRecursion.lookup value (suc pred) index (Fin.cons front Fin.elim0) ⟨symm hi'⟩ hs
   obtain ⟨h⟩ := InternalApplicationStepPeelSupportProof.andIntro hbound hlookup
   exact ⟨orLeft h⟩
 · intro Theta inc ht
   apply tailCases count suffix pred value _ ht
   intro beta j Xi suffixIndex suffixCount hj hf
   have hi' := renameInto (weakenProof hi inc) j Xi hj
   simp only [eqnRename,sucRelabel] at hi'
   obtain ⟨hi'⟩ := hi'
   obtain ⟨hpred⟩ := InternalApplicationStepPeelSupportProof.andLeft hf
   have he : Nonempty (Derivation body Xi (eqn (index.relabel j) (add (suc (count.relabel j)) suffixIndex))) :=
     ⟨trans hi' (trans (congSuc hpred) (symm (leftSuccessor (count.relabel j) suffixIndex)))⟩
   have htail := tailIntro (suc (count.relabel j)) (suffix.relabel j) (index.relabel j) (value.relabel j)
     suffixIndex suffixCount (InternalApplicationStepPeelSupportProof.andIntro he (InternalApplicationStepPeelSupportProof.andRight hf))
   simp only [resultRename,sucRelabel]
   obtain ⟨htail⟩ := htail
   exact ⟨orRight htail⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupLiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupLiftProof

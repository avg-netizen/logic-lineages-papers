module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphCompositionFunctionalityProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open OriginalPositionStructuralKeyOpeningDefinitions
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)

/-- Proof-only assembly using the independently proved deletion theorem.
The eventual public exact alias supplies that theorem, never a user premise. -/
theorem fromDeletion (deletion : OriginalAllPositionContextDeleteTargets.ActualDeletionInsertion) : ActualOpening := by
 intro p H G W body alpha Delta value parameter cutoff mark psi hs hw hr ho consume
 apply OriginalIndexedObserverRangeSyntaxProof.rangeCases cutoff parameter psi hr
 intro beta j Theta count hj hfields
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs'
 have hw' := renameInto hw j Theta hj
 simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
   graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 apply OriginalPositionStructuralKeyOpeningQueryProof.atCount deletion p H G W
   (value.relabel j) (parameter.relabel j) (cutoff.relabel j) (mark.relabel j) count (psi.relabel j)
   hs' hw' (andLeft hfields) (andRight hfields) ho'
 intro gamma k Xi context runtime erasedType deleted erased erasedParam keyValue rank hk opened
 have inc : ∀ h ∈ Delta, h.relabel (k ∘ j) ∈ Xi := by
   intro h hh
   simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (h.relabel j) (hj h hh)
 have ho : Nonempty (Derivation body Xi
   (Opened p H G W (value.relabel (k ∘ j)) (parameter.relabel (k ∘ j))
     (cutoff.relabel (k ∘ j)) (mark.relabel (k ∘ j)) context runtime erasedType deleted erased erasedParam keyValue rank)) := by
   simpa only [Term.relabel_relabel] using opened
 have conclusion := consume gamma (k ∘ j) Xi context runtime erasedType deleted erased erasedParam keyValue rank inc ho
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using conclusion

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningRangeProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningRangeProof

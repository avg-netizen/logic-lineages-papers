module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open OriginalTransparentLambdaValidity
open OriginalTransparentLambdaFinalLogicProof
open OriginalFinalOtherValidityTagProof OriginalFinalOtherValidityLocalProof

/-- Full-output source exposure at the SAME existing final tuple. The only
arithmetic antecedent is the original OTHER-tag acceptance graph. -/
theorem actualOriginalFinalOtherSourceValidity :
    OriginalFinalOtherValidityTargets.ActualOriginalFinalOtherSourceValidity := by
  intro p body alpha Delta out raw parameter
  let O := graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one raw
  have ho : Nonempty (Derivation body (O :: Delta) O) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h2 := otherNotTwo raw ho
  have h1 := otherNotOne raw ho
  let N := OriginalHereditaryValidity.normalizedData p.base
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hsource := (OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws p).1.2.2
  have hlocal := iffCompose
    (andIff (targetAcceptance p.base raw parameter h2 h1)
      (sourceAcceptance p.base raw parameter h2 h1))
    (mergeTargetSource (graph2 N.oldSource (numeral 1) raw parameter)
      (graph2 N.oldTarget (numeral 1) raw parameter))
  obtain ⟨h⟩ := iffCompose (hsource body alpha (O :: Delta) out raw parameter)
    (iffCompose (conjunctionEquation (targetValidator p.base) (sourceValidator p.base) xs out)
      (booleanIff out hlocal))
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Full-output target exposure at that IDENTICAL final tuple and parameter,
without source/window assumptions or an output-one restriction. -/
theorem actualOriginalFinalOtherTargetValidity :
    OriginalFinalOtherValidityTargets.ActualOriginalFinalOtherTargetValidity := by
  intro p body alpha Delta out raw parameter
  let O := graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one raw
  have ho : Nonempty (Derivation body (O :: Delta) O) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htarget := (OriginalLambdaTraversalSelectionValidityProof.finalInternalLaws p).1.1
  obtain ⟨h⟩ := iffCompose (htarget body alpha (O :: Delta) out raw parameter)
    (targetOutput p.base out raw parameter (otherNotTwo raw ho) (otherNotOne raw ho))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityProof

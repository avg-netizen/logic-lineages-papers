module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyActiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof (valueUnique)
open UniformCertificateCompletion OriginalStructuralClassKeyDefinitions
open OriginalStructuralClassKeyActiveProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Shared structural child computations are sufficient; the actual guarded
parent computations are reduced to the pre-refinement traversal, whose
constructor graph functionality proves the resulting equality. -/
theorem actualOriginalStructuralClassKeyApplicationCongruence :
    OriginalStructuralClassKeyTargets.ActualOriginalStructuralClassKeyApplicationCongruence := by
  intro p H G W body alpha Delta value other d e fn arg otherFn otherArg fOut aOut out otherOut parameter
  let A := Active p H G W value parameter ⊓
      (Active p H G W other parameter ⊓
        (OriginalLambdaTraversalInternal.ApplicationFields value d e fn arg ⊓
          (OriginalLambdaTraversalInternal.ApplicationFields other d e otherFn otherArg ⊓
            (graph2 (core p H G W) fOut fn parameter ⊓
              (graph2 (core p H G W) fOut otherFn parameter ⊓
                (graph2 (core p H G W) aOut arg parameter ⊓
                  (graph2 (core p H G W) aOut otherArg parameter ⊓
                    (graph2 (key p H G W) out value parameter ⊓
                      graph2 (key p H G W) otherOut other parameter))))))))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 := andRight h
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  have h5 := andRight h4
  have h6 := andRight h5
  have h7 := andRight h6
  have h8 := andRight h7
  have hc := keyToCore p H G W value out parameter (andLeft h) (andLeft h8)
  have ho := keyToCore p H G W other otherOut parameter (andLeft h1) (andRight h8)
  have hp := OriginalLambdaTraversalInternalApplicationProof.applicationForward
    (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
    value d e fn arg parameter fOut aOut out (andLeft h2) (andLeft h4) (andLeft h6) hc
  have hq := OriginalLambdaTraversalInternalApplicationProof.applicationForward
    (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
    other d e otherFn otherArg parameter fOut aOut otherOut (andLeft h3) (andLeft h5) (andLeft h7) ho
  obtain ⟨he⟩ := valueUnique InternalApplicationCertificateConstructors.application out otherOut
    (Fin.cons d (Fin.cons e (Fin.cons fOut (Fin.cons aOut Fin.elim0)))) hp hq
  have he' : Derivation body (A :: Delta) (equal out otherOut) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using he
  exact ⟨Derivation.implicationIntroduction he'⟩

theorem actualOriginalStructuralClassKeyLambdaCongruence :
    OriginalStructuralClassKeyTargets.ActualOriginalStructuralClassKeyLambdaCongruence := by
  intro p H G W body alpha Delta value other d e rawBody otherBody bodyOut out otherOut parameter childParameter
  let A := Active p H G W value parameter ⊓
      (Active p H G W other parameter ⊓
        (OriginalLambdaTraversalInternal.LambdaFields value d e rawBody parameter childParameter ⊓
          (OriginalLambdaTraversalInternal.LambdaFields other d e otherBody parameter childParameter ⊓
            (graph2 (core p H G W) bodyOut rawBody childParameter ⊓
              (graph2 (core p H G W) bodyOut otherBody childParameter ⊓
                (graph2 (key p H G W) out value parameter ⊓
                  graph2 (key p H G W) otherOut other parameter))))))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 := andRight h
  have h2 := andRight h1
  have h3 := andRight h2
  have h4 := andRight h3
  have h5 := andRight h4
  have h6 := andRight h5
  have hc := keyToCore p H G W value out parameter (andLeft h) (andLeft h6)
  have ho := keyToCore p H G W other otherOut parameter (andLeft h1) (andRight h6)
  have hp := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
    (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
    value d e rawBody parameter childParameter bodyOut out (andLeft h2) (andLeft h4) hc
  have hq := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
    (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
    other d e otherBody parameter childParameter bodyOut otherOut (andLeft h3) (andLeft h5) ho
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.constructor out otherOut
    (Fin.cons d (Fin.cons e (Fin.cons bodyOut Fin.elim0))) hp hq
  have he' : Derivation body (A :: Delta) (equal out otherOut) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,InternalTagArithmeticSyntaxProof.eqn] using he
  exact ⟨Derivation.implicationIntroduction he'⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCongruenceProof

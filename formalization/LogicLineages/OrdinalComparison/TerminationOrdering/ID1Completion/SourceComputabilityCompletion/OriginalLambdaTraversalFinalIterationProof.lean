module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z)
open InternalParameterizedBoundedDescentNormalizer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The original bounded transition takes an actual valid, same-type,
nonincreasing representative output. Strict descent and equality use the
literal original choice guard, including its rejected-equality case. -/
theorem transitionValue (R V : Program 2)
    (out input typ parameter : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R out input parameter)))
    (hv : Nonempty (Derivation body Delta (validGraph V out parameter)))
    (ho : Nonempty (Derivation body Delta (leftGraph typ out)))
    (hi : Nonempty (Derivation body Delta (leftGraph typ input)))
    (hb : Nonempty (Derivation body Delta (atMost out input))) :
    Nonempty (Derivation body Delta (transitionGraph R V out input parameter)) := by
  have hc := OriginalApplicationSidecarTransitionChoiceProof.chooseBounded V out input typ parameter hv ho hi hb
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply compositionValue (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    out xs (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))) hc
  intro i
  exact Fin.cases hr (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

/-- One actual transition followed by a derived actual fixed output pays
all original value+1 fuel. The runtime parameter never changes. -/
theorem normalizerAtFixedOutput (R V : Program 2)
    (out input parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (transitionGraph R V out input parameter)))
    (hf : Nonempty (Derivation body Delta (transitionGraph R V out out parameter))) :
    Nonempty (Derivation body Delta (normalizerGraph R V out input parameter)) := by
  have fixed := InternalParameterizedNumericIterationLawsProof.fixedValue
    (transition R V) input out parameter hf
  have run := InternalParameterizedNumericIterationLawsProof.frontSuccBackward
    (transition R V) out input input out parameter ht fixed
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply compositionValue (InternalParameterizedNumericIteration.repeatP (transition R V))
    (Fin.cons (.composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    out xs (Fin.cons (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0))) run
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2))
      (suc input) xs (Fin.cons input Fin.elim0) (successorValue (Fin.cons input Fin.elim0))
    intro j
    obtain rfl := Fin.eq_zero j
    exact projectionValue (0 : Fin 2) xs
  · exact projectionValue (0 : Fin 2) xs
  · exact projectionValue (1 : Fin 2) xs

/-- At accepted source inputs the unchanged fallback representative selects
the actual bounded normalizer, with its full output and exact-one guard. -/
theorem selectedAtFixedOutput (R V : Program 2)
    (out input parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 V InternalOriginalStepGuard.one input parameter)))
    (ht : Nonempty (Derivation body Delta (transitionGraph R V out input parameter)))
    (hf : Nonempty (Derivation body Delta (transitionGraph R V out out parameter))) :
    Nonempty (Derivation body Delta
      (InternalOriginalUniformDescentSelection.representativeGraph R V out input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hg := InternalApplicationStepPeelSupportProof.sameAccept V (InternalLessThan.constantOne 2)
    (suc z) xs hv (InternalLessThanSupportProof.oneConstantValue xs)
  exact InternalAcceptanceBranchProof.successorBranchIntro
    (InternalApplicationValidityStack.exactOne V) R (normalizer R V) out z xs hg
    (normalizerAtFixedOutput R V out input parameter ht hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalIterationProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Actual transition fixedness supplies the original value+1 iteration,
through its real projection/successor composition and unchanged parameter. -/
theorem normalizerFixedValue (R V : Program 2)
    (input parameter : OrdinaryArithmetic.Term alpha)
    (hf : Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph R V input input parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.normalizerGraph R V input input parameter)) := by
  have hr := InternalParameterizedNumericIterationLawsProof.fixedValue
    (InternalParameterizedBoundedDescentNormalizer.transition R V) (suc input) input parameter hf
  apply compositionValue
    (InternalParameterizedNumericIteration.repeatP (InternalParameterizedBoundedDescentNormalizer.transition R V))
    (Fin.cons (.composition .succ (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)))
    input (Fin.cons input (Fin.cons parameter Fin.elim0))
    (Fin.cons (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0))) hr
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.cases ?_ (fun k => Fin.elim0 k) i) i) i
  · apply compositionValue .succ (fun _ : Fin 1 => .projection (0 : Fin 2))
      (suc input) (Fin.cons input (Fin.cons parameter Fin.elim0))
      (Fin.cons input Fin.elim0) (successorValue (Fin.cons input Fin.elim0))
    intro j
    obtain rfl := Fin.eq_zero j
    exact projectionValue (0 : Fin 2) (Fin.cons input (Fin.cons parameter Fin.elim0))
  · exact projectionValue (0 : Fin 2) (Fin.cons input (Fin.cons parameter Fin.elim0))
  · exact projectionValue (1 : Fin 2) (Fin.cons input (Fin.cons parameter Fin.elim0))

/-- Only a derived valid fixed input selects the bounded branch. No assertion
about arbitrary invalid-input fallback or whole-fold idempotence is made. -/
theorem selectedFixedValue (R V : Program 2)
    (input parameter : OrdinaryArithmetic.Term alpha)
    (hv : Nonempty (Derivation body Delta (graph2 V (suc z) input parameter)))
    (hf : Nonempty (Derivation body Delta
      (InternalParameterizedBoundedDescentNormalizer.transitionGraph R V input input parameter))) :
    Nonempty (Derivation body Delta
      (InternalOriginalUniformDescentSelection.representativeGraph R V input input parameter)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hg := InternalApplicationStepPeelSupportProof.sameAccept V (InternalLessThan.constantOne 2)
    (suc z) xs hv (InternalLessThanSupportProof.oneConstantValue xs)
  exact InternalAcceptanceBranchProof.successorBranchIntro
    (InternalApplicationValidityStack.exactOne V) R
    (InternalParameterizedBoundedDescentNormalizer.normalizer R V) input z xs hg
    (normalizerFixedValue R V input parameter hf)

/-- A supplied actual self-output gives the entire arbitrary-output equality
iff by Program functionality and output transport, not semantic reflection. -/
theorem selfOutputIff (p : Program 2)
    (out input parameter : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta (graph2 p input input parameter))) :
    Nonempty (Derivation body Delta ((graph2 p out input parameter).iff (eqn out input))) := by
  let G := graph2 p out input parameter
  let E := eqn out input
  obtain ⟨forward⟩ := valueUnique p out input (Fin.cons input (Fin.cons parameter Fin.elim0))
    (show Nonempty (Derivation body (G :: Delta) G) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (withHyp hi G)
  have he : Derivation body (E :: Delta) E := Derivation.hypothesis List.mem_cons_self
  obtain ⟨backward⟩ := outputTransport p input out (Fin.cons input (Fin.cons parameter Fin.elim0))
    ⟨symm he⟩ (withHyp hi E)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafIterationProof

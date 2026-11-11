module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalQuotientComparisonProof (orLeft)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternal (BooleanOutput TagIs)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem booleanOneEquation (A : Formula alpha) :
    Nonempty (Derivation body Gamma ((BooleanOutput (numeral 1) A).iff A)) := by
  let L := equal (numeral 1 : OTerm alpha) (numeral 1) ⊓ A
  let R := equal (numeral 1 : OTerm alpha) z ⊓ A.not
  have hl : Derivation body (L :: BooleanOutput (numeral 1) A :: Gamma) A :=
    Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
  have hr : Derivation body (R :: BooleanOutput (numeral 1) A :: Gamma) A := by
    have hh : Derivation body (R :: BooleanOutput (numeral 1) A :: Gamma) R :=
      Derivation.hypothesis List.mem_cons_self
    have he : Derivation body (R :: BooleanOutput (numeral 1) A :: Gamma) (eqn (suc z) z) := by
      simpa only [R,equalEqn,numeral] using Derivation.conjunctionLeft hh
    exact Derivation.explosion (zeroNeSuc (symm he))
  have hf : Derivation body (BooleanOutput (numeral 1) A :: Gamma) A :=
    disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction hr)
  have he : Derivation body (A :: Gamma) (equal (numeral 1 : OTerm alpha) (numeral 1)) := by
    rw [equalEqn]
    exact refl _
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction (orLeft (Derivation.conjunctionIntroduction he
      (Derivation.hypothesis List.mem_cons_self))))⟩

theorem booleanAcceptance {P A : Formula alpha}
    (h : Nonempty (Derivation body Gamma (P.iff (BooleanOutput (numeral 1) A)))) :
    Nonempty (Derivation body Gamma (P.iff A)) :=
  iffCompose h (booleanOneEquation A)

/-- The literal variable-test branch is zero whenever the actual tag is not zero. -/
theorem nonvariableControl (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (TagIs 0 raw).not)) :
    Nonempty (Derivation body Gamma (graph2 OriginalVariableLeaves.variableTag z raw parameter)) := by
  let A := graph1 OriginalConstructorLeaf.variableTest (numeral 1) raw
  have ht := sameRightRecover OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1)
    z (Fin.cons raw Fin.elim0)
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (InternalLessThanSupportProof.zeroConstantValue (Fin.cons raw Fin.elim0))
  obtain ⟨hn'⟩ := addAssumption hn A
  obtain ⟨ht⟩ := ht
  have htest : Nonempty (Derivation body Gamma A.not) :=
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn' ht)⟩
  have hz := OriginalTransparentLambdaValidityInternalBooleanProof.sameReject
    OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1)
    (Fin.cons raw Fin.elim0) htest
  exact unaryValue OriginalConstructorLeaf.variableTest (.projection 0) z raw
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) hz
    (projectionValue 0 (Fin.cons raw (Fin.cons parameter Fin.elim0)))

theorem variableBranchOff (old yes : Program 2) (out raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (TagIs 0 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (InternalAcceptance.branch OriginalVariableLeaves.variableTag old yes)
        out raw parameter).iff (graph2 old out raw parameter))) := by
  let A := graph2 (InternalAcceptance.branch OriginalVariableLeaves.variableTag old yes) out raw parameter
  let B := graph2 old out raw parameter
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hc := nonvariableControl raw parameter hn
  obtain ⟨hf⟩ := zeroBranchElim OriginalVariableLeaves.variableTag old yes out xs
    (addAssumption hc A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := zeroBranchIntro OriginalVariableLeaves.variableTag old yes out xs
    (addAssumption hc B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The member remains the SAME original member, sliced at the SAME context. -/
theorem normalizedMemberAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (out typ parameter context gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).member
        out typ parameter).iff
        (graph2 (InternalOriginalUniformContextMembership.contextMember p.base.member) out typ context))) := by
  obtain ⟨hs⟩ := InternalOriginalUniformContextMembershipInternalProof.actualOriginalUniformMembershipSlice
    p.base.member body alpha Gamma out typ parameter context gamma
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination hs hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof

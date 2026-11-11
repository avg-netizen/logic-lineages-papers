module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalUniformDescentSelection (Data)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalBranchSupportProof
open OriginalTransparentLambdaValidityInternalBranchValueProof
open OriginalTransparentLambdaValidityInternalSourceCheckProof (sourceCheck)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaFinalLogicProof
open OriginalFinalOtherValidityRecurrenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The accepted original callback dispatch laws retain the ENTIRE opaque
leaf output off both structural tags, even when it is not Boolean. -/
theorem rootOtherEquation (old lambda : Program 2) (out raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (rootDispatch old lambda) out raw parameter).iff
        (graph2 old out raw parameter))) := by
  let A := graph2 (rootDispatch old lambda) out raw parameter
  let B := graph2 old out raw parameter
  obtain ⟨hf⟩ := dispatchOpaque old lambda out raw parameter
    (addAssumption h2 A) (addAssumption h1 A)
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := dispatchOpaqueValue old lambda out raw parameter
    (addAssumption h2 B) (addAssumption h1 B)
    (show Nonempty (Derivation body (B :: Gamma) B) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem sourceAcceptance (rawData : Data) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (sourceValidator rawData) (numeral 1) raw parameter).iff
        (graph2 (normalizedData rawData).oldSource (numeral 1) raw parameter ⊓
          graph2 (normalizedData rawData).oldTarget (numeral 1) raw parameter))) := by
  let N := normalizedData rawData
  exact iffCompose
    (acceptanceOtherEquation (sourceRoot N) (targetRoot N) N.member raw parameter h2 h1)
    (andIff (rootOtherEquation N.oldSource (sourceCheck N) (numeral 1) raw parameter h2 h1)
      (rootOtherEquation N.oldTarget lambdaShape (numeral 1) raw parameter h2 h1))

/-- The target's auxiliary constant-one root is discharged internally.
No source-window membership is introduced. -/
theorem targetRootFactors (data : Data) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetRoot data) (numeral 1) raw parameter ⊓
          graph2 (InternalLessThan.constantOne 2) (numeral 1) raw parameter).iff
        (graph2 data.oldTarget (numeral 1) raw parameter))) := by
  let A := graph2 (targetRoot data) (numeral 1) raw parameter ⊓
    graph2 (InternalLessThan.constantOne 2) (numeral 1) raw parameter
  let B := graph2 data.oldTarget (numeral 1) raw parameter
  obtain ⟨he⟩ := rootOtherEquation data.oldTarget lambdaShape (numeral 1) raw parameter h2 h1
  have hf : Derivation body (A :: Gamma) B :=
    Derivation.implicationElimination (InternalBetaTotalityProof.addHyp (Derivation.conjunctionLeft he) A)
      (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨hone⟩ := (InternalLessThanSupportProof.oneConstantValue
    (body := body) (Gamma := B :: Gamma) (Fin.cons raw (Fin.cons parameter Fin.elim0)))
  have hb : Derivation body (B :: Gamma) A :=
    Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp (Derivation.conjunctionRight he) B)
        (Derivation.hypothesis List.mem_cons_self)) hone
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem targetAcceptance (rawData : Data) (raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetValidator rawData) (numeral 1) raw parameter).iff
        (graph2 (normalizedData rawData).oldTarget (numeral 1) raw parameter))) := by
  let N := normalizedData rawData
  exact iffCompose
    (acceptanceOtherEquation (targetRoot N) (InternalLessThan.constantOne 2)
      (InternalLessThan.constantOne 2) raw parameter h2 h1)
    (targetRootFactors N raw parameter h2 h1)

theorem targetOutput (rawData : Data) (out raw parameter : OTerm alpha)
    (h2 : Nonempty (Derivation body Gamma (TagIs 2 raw).not))
    (h1 : Nonempty (Derivation body Gamma (TagIs 1 raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (targetValidator rawData) out raw parameter).iff
        (BooleanOutput out (graph2 (normalizedData rawData).oldTarget (numeral 1) raw parameter)))) := by
  let N := normalizedData rawData
  exact iffCompose
    (outputOtherEquation (targetRoot N) (InternalLessThan.constantOne 2)
      (InternalLessThan.constantOne 2) out raw parameter h2 h1)
    (booleanIff out (targetRootFactors N raw parameter h2 h1))

/-- Retain source AND target; the separate target conjunct is redundant
only because the internally exposed source already contains that same leaf. -/
theorem mergeTargetSource (S T : Formula alpha) :
    Nonempty (Derivation body Gamma ((T ⊓ (S ⊓ T)).iff (S ⊓ T))) := by
  have hf : Derivation body (T ⊓ (S ⊓ T) :: Gamma) (S ⊓ T) :=
    Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)
  have h : Derivation body (S ⊓ T :: Gamma) (S ⊓ T) :=
    Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction (Derivation.conjunctionRight h) h))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityLocalProof

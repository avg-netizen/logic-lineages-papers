module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargetLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceFactorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalOriginalUniformDescentSelection (Data)
open InternalBetaTotalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalTransparentLambdaValidityInternal (SourceLambdaRootFactors LambdaShape)
open OriginalTransparentLambdaValidityInternalSourceCheckProof
open OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
open OriginalTransparentLambdaFinal OriginalTransparentLambdaFinalLogicProof
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The root formula mentions precisely the member field; neither old
validity leaf nor representative is inspected by it. -/
theorem sourceRootMemberIdentity (left right : Data) (hm : left.member = right.member)
    (raw parameter : OTerm alpha) :
    SourceLambdaRootFactors left raw parameter = SourceLambdaRootFactors right raw parameter := by
  simp only [SourceLambdaRootFactors,hm]

theorem sourceRootShape (data : Data) (raw parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter))) :
    Nonempty (Derivation body Gamma (LambdaShape raw)) := by
  have hc := sourceCheckValue data raw parameter hf
  have hs := andLeft (conjunctionRecover _ _ (Fin.cons raw (Fin.cons parameter Fin.elim0)) hc)
  exact shapeRecover raw parameter hs

/-- Source root shape supplies the target root shape. Preserve BOTH child
calls while reordering these exact factors; no source-implies-target law is
used, since the final source really retains the HT AND HS conjunction. -/
theorem mergeFactors (data : Data) (raw parameter : OTerm alpha)
    (targetChild sourceChild : Formula alpha) :
    Nonempty (Derivation body Gamma
      (((LambdaShape raw ⊓ targetChild) ⊓
          (SourceLambdaRootFactors data raw parameter ⊓ sourceChild)).iff
        (SourceLambdaRootFactors data raw parameter ⊓ (targetChild ⊓ sourceChild)))) := by
  let A := (LambdaShape raw ⊓ targetChild) ⊓
    (SourceLambdaRootFactors data raw parameter ⊓ sourceChild)
  let B := SourceLambdaRootFactors data raw parameter ⊓ (targetChild ⊓ sourceChild)
  have ha : Derivation body (A :: Gamma) A := Derivation.hypothesis List.mem_cons_self
  have hf : Derivation body (A :: Gamma) B :=
    Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionRight ha))
      (Derivation.conjunctionIntroduction (Derivation.conjunctionRight (Derivation.conjunctionLeft ha))
        (Derivation.conjunctionRight (Derivation.conjunctionRight ha)))
  have hb : Derivation body (B :: Gamma) B := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hshape⟩ := sourceRootShape data raw parameter ⟨Derivation.conjunctionLeft hb⟩
  have hr : Derivation body (B :: Gamma) A :=
    Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction hshape (Derivation.conjunctionLeft (Derivation.conjunctionRight hb)))
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hb)
        (Derivation.conjunctionRight (Derivation.conjunctionRight hb)))
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hr)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceFactorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalSourceFactorProof

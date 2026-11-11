module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open OriginalHereditaryValidityInternalNodeSupportProof (weakenProof)
open OriginalTransparentLambdaFinal
open OriginalTransparentLambdaFinalChildSyntaxProof OriginalTransparentLambdaFinalChildSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Change only the final validator graph inside the original, connected
lambda witness block. Every actual selector and context-extension witness
is retained literally. The input law is an internal derivation supplier. -/
theorem childMap (valid next : Program 2) (raw parameter : OTerm alpha)
    (law : ∀ (beta : Type) (Delta : List (Formula beta)) (child childParameterCode : OTerm beta),
      Nonempty (Derivation body Delta
        ((graph2 valid (numeral 1) child childParameterCode).imp
          (graph2 next (numeral 1) child childParameterCode))))
    (h : Nonempty (Derivation body Gamma (FinalLambdaChild valid raw parameter))) :
    Nonempty (Derivation body Gamma (FinalLambdaChild next raw parameter)) := by
  apply finalChildCases valid raw parameter _ h
  intro beta j Delta state child childParameterCode _ fields
  rw [finalChildRename]
  obtain ⟨he⟩ := law beta Delta child childParameterCode
  obtain ⟨hv⟩ := andRight (andRight (andRight fields))
  exact finalChildIntro next (raw.relabel j) (parameter.relabel j) state child childParameterCode
    (andIntro (andLeft fields) (andIntro (andLeft (andRight fields))
      (andIntro (andLeft (andRight (andRight fields)))
        ⟨Derivation.implicationElimination he hv⟩)))

theorem childIff (valid next : Program 2) (raw parameter : OTerm alpha)
    (law : ∀ (beta : Type) (Delta : List (Formula beta)) (child childParameterCode : OTerm beta),
      Nonempty (Derivation body Delta
        ((graph2 valid (numeral 1) child childParameterCode).iff
          (graph2 next (numeral 1) child childParameterCode)))) :
    Nonempty (Derivation body Gamma
      ((FinalLambdaChild valid raw parameter).iff (FinalLambdaChild next raw parameter))) := by
  let A := FinalLambdaChild valid raw parameter
  let B := FinalLambdaChild next raw parameter
  obtain ⟨hf⟩ := childMap (body := body) (Gamma := A :: Gamma) valid next raw parameter
    (fun beta Delta child childParameterCode => andLeft (law beta Delta child childParameterCode))
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := childMap (body := body) (Gamma := B :: Gamma) next valid raw parameter
    (fun beta Delta child childParameterCode => andRight (law beta Delta child childParameterCode))
    (show Nonempty (Derivation body (B :: Gamma) B) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- Extract both calls using the SAME original lambda-child witnesses. -/
theorem childConjunctionForward (left right : Program 2) (raw parameter : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (FinalLambdaChild (InternalAcceptance.conjunction left right) raw parameter))) :
    Nonempty (Derivation body Gamma
      (FinalLambdaChild left raw parameter ⊓ FinalLambdaChild right raw parameter)) := by
  apply finalChildCases (InternalAcceptance.conjunction left right) raw parameter _ h
  intro beta j Delta state child childParameterCode _ fields
  change Nonempty (Derivation body Delta
    ((FinalLambdaChild left raw parameter).relabel j ⊓
      (FinalLambdaChild right raw parameter).relabel j))
  simp only [finalChildRename]
  have hv := conjunctionRecover left right (Fin.cons child (Fin.cons childParameterCode Fin.elim0))
    (andRight (andRight (andRight fields)))
  exact andIntro
    (finalChildIntro left (raw.relabel j) (parameter.relabel j) state child childParameterCode
      (andIntro (andLeft fields) (andIntro (andLeft (andRight fields))
        (andIntro (andLeft (andRight (andRight fields))) (andLeft hv)))))
    (finalChildIntro right (raw.relabel j) (parameter.relabel j) state child childParameterCode
      (andIntro (andLeft fields) (andIntro (andLeft (andRight fields))
        (andIntro (andLeft (andRight (andRight fields))) (andRight hv)))))

/-- Fuse independently opened child blocks by original initial/body/parameter
graph functionality. The right witness cannot choose another body or Gamma. -/
theorem childConjunctionBackward (left right : Program 2) (raw parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (FinalLambdaChild left raw parameter)))
    (hr : Nonempty (Derivation body Gamma (FinalLambdaChild right raw parameter))) :
    Nonempty (Derivation body Gamma
      (FinalLambdaChild (InternalAcceptance.conjunction left right) raw parameter)) := by
  apply finalChildCases left raw parameter _ hl
  intro beta j Delta state child childParameterCode hj fields
  rw [finalChildRename]
  have hr' := renameInto hr j Delta hj
  rw [finalChildRename] at hr'
  have hright := finalChildAt right (raw.relabel j) (parameter.relabel j) state child childParameterCode
    (andLeft fields) (andLeft (andLeft (andRight fields)))
    (andLeft (andRight (andRight fields))) hr'
  have hc := conjunctionAccept left right (Fin.cons child (Fin.cons childParameterCode Fin.elim0))
    (andRight (andRight (andRight fields))) hright
  exact finalChildIntro (InternalAcceptance.conjunction left right)
    (raw.relabel j) (parameter.relabel j) state child childParameterCode
    (andIntro (andLeft fields) (andIntro (andLeft (andRight fields))
      (andIntro (andLeft (andRight (andRight fields))) hc)))

theorem childConjunction (left right : Program 2) (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((FinalLambdaChild (InternalAcceptance.conjunction left right) raw parameter).iff
        (FinalLambdaChild left raw parameter ⊓ FinalLambdaChild right raw parameter))) := by
  let A := FinalLambdaChild (InternalAcceptance.conjunction left right) raw parameter
  let B := FinalLambdaChild left raw parameter ⊓ FinalLambdaChild right raw parameter
  obtain ⟨hf⟩ := childConjunctionForward (body := body) (Gamma := A :: Gamma) left right raw parameter
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hb : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := childConjunctionBackward left right raw parameter (andLeft hb) (andRight hb)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildTransportProof

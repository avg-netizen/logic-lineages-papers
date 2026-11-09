module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationTypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem suppliedOutputTypes (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (oldStep : Program 4) (sigma tau : Ty)
    (x y a certificate out other parameter gammaCode : OTerm α)
    (h : Nonempty (Derivation body Delta
      (Application.parameterPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData base) oldStep sigma tau x y a certificate out other parameter gammaCode))) :
    Nonempty (Derivation body Delta
      (Application.typedOutputs (normalizeData base) tau out other parameter)) := by
  have hp := andLeft h
  have hcore := andRight h
  have hx := andLeft hcore
  have ha := andLeft (andRight hcore)
  have he := andLeft (andRight (andRight hcore))
  have hj := andRight (andRight (andRight hcore))
  have hy := TypingProof.typedPropagation (normalizeData base) oldStep x y certificate
    (numeral (typeNumber (.arrow sigma tau))) parameter hx he
  have ho := InternalOriginalUniformApplicationTypingProof.runtimeApplicationTyped
    n arity base hc symbols S table hS sigma tau parameter gammaCode x a out
    (andIntro hp (andIntro hx (andIntro ha (andLeft hj))))
  have hv := InternalOriginalUniformApplicationTypingProof.runtimeApplicationTyped
    n arity base hc symbols S table hS sigma tau parameter gammaCode y a other
    (andIntro hp (andIntro hy (andIntro ha (andRight hj))))
  exact andIntro ho hv

theorem actualOriginalUniformApplicationEdgeTypedOutputs :
    ApplicationTargets.ActualOriginalUniformApplicationEdgeTypedOutputs := by
  intro n arity base hc symbols S table hS oldStep body α Delta sigma tau
    x y a certificate out other lifted parameter gammaCode
  let P := Application.liftPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (normalizeData base) oldStep sigma tau x y a certificate out other lifted parameter gammaCode
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := suppliedOutputTypes n arity base hc symbols S table hS oldStep sigma tau
    x y a certificate out other parameter gammaCode (andLeft hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationTypingProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalApplicationStepPeelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The same edge supplies the target function's type; actualJ types both
outputs using the original raw argument and the shared parameter. -/
theorem applicationTypedOutputs (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (corePremises data oldStep arrow d e x y a certificate out other parameter))) :
    Nonempty (Derivation body Gamma (typedOutputs data e out other parameter)) := by
  have har := andLeft (andLeft h)
  have hm := andRight (andLeft h)
  have hi := andRight h
  have hx := andLeft hi
  have ha := andLeft (andRight hi)
  have he := andLeft (andRight (andRight hi))
  have hj := andRight (andRight (andRight hi))
  have hy := InternalParameterizedQuotientEdgeCheckerTypedProof.typedPropagation
    data oldStep x y certificate arrow parameter hx he
  exact andIntro
    (InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped
      data arrow d e x a out parameter
      (andIntro har (andIntro hm (andIntro hx (andIntro ha (andLeft hj))))))
    (InternalOriginalUniformApplicationTypingApplicationProof.applicationTyped
      data arrow d e y a other parameter
      (andIntro har (andIntro hm (andIntro hy (andIntro ha (andRight hj))))))

theorem actualParameterizedCanonicalQuotientEdgeApplicationTypedOutputs :
    InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets.ActualParameterizedCanonicalQuotientEdgeApplicationTypedOutputs := by
  intro body data oldStep α Delta arrow d e x y a certificate out other parameter
  let P := corePremises data oldStep arrow d e x y a certificate out other parameter
  obtain ⟨h⟩ := applicationTypedOutputs (body := body) (Gamma := P :: Delta)
    data oldStep arrow d e x y a certificate out other parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTypedProof

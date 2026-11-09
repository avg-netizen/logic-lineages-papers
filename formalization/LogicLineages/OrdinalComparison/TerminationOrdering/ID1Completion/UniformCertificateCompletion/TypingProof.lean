module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingSelectorsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationStepPeelSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open UniformCertificateCompletion.SupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem typedPropagation (data : Data) (oldStep : Program 4)
    (x y certificate typ parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ parameter)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ parameter)) := by
  apply programCases source (Fin.cons certificate Fin.elim0)
    (typedAccepted data y typ parameter)
  intro β j Delta s hj hs
  rw [typedRename]
  simp only [consTermRename,emptyRename] at hs
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  exact withSource data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j) s
    (typ.relabel j) (parameter.relabel j) ht' he' hs

theorem actualParameterizedQuotientEdgeTypedPropagation :
    Targets.ActualParameterizedQuotientEdgeTypedPropagation := by
  intro data oldStep body α Delta x y certificate typ parameter
  let premise := typedAccepted data x typ parameter ⊓ edgeAccepted data oldStep x y certificate parameter
  have hp : Nonempty (Derivation body (premise :: Delta) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := typedPropagation data oldStep x y certificate typ parameter (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof

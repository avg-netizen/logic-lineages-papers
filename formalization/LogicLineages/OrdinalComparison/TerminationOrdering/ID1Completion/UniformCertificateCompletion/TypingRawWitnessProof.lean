module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingCoreProof
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

theorem rawTyped (data : Data) (oldStep : Program 4)
    (x y certificate s t k typ parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ parameter)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)))
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0)
    (typedAccepted data y typ parameter)
  intro β j Delta tag hj hl
  rw [typedRename]
  simp only [consTermRename,emptyRename] at hl
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hf' := renameInto hf j Delta hj
  rw [selectorsRename] at hf'
  exact rawWithTag data oldStep (x.relabel j) (y.relabel j) (s.relabel j) (t.relabel j)
    (k.relabel j) (typ.relabel j) tag (parameter.relabel j) ht'
    (checkerRecover data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j)
      (s.relabel j) (t.relabel j) (k.relabel j) (parameter.relabel j) hf' he') hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingRawWitnessProof
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

theorem withSourceTarget (data : Data) (oldStep : Program 4)
    (x y certificate s t typ parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ parameter)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)))
    (hs : Nonempty (Derivation body Gamma (graph1 source s certificate)))
    (hv : Nonempty (Derivation body Gamma (graph1 target t certificate))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ parameter)) := by
  apply programCases step (Fin.cons certificate Fin.elim0)
    (typedAccepted data y typ parameter)
  intro β j Delta k hj hk
  rw [typedRename]
  simp only [consTermRename,emptyRename] at hk
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hv' := renameInto hv j Delta hj
  rw [graph1Rename] at hv'
  exact rawTyped data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j)
    (s.relabel j) (t.relabel j) k (typ.relabel j) (parameter.relabel j) ht' he'
    (andIntro hs' (andIntro hv' hk))

theorem withSource (data : Data) (oldStep : Program 4)
    (x y certificate s typ parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ parameter)))
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)))
    (hs : Nonempty (Derivation body Gamma (graph1 source s certificate))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ parameter)) := by
  apply programCases target (Fin.cons certificate Fin.elim0)
    (typedAccepted data y typ parameter)
  intro β j Delta t hj hv
  rw [typedRename]
  simp only [consTermRename,emptyRename] at hv
  have ht' := renameInto ht j Delta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  exact withSourceTarget data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j)
    (s.relabel j) t (typ.relabel j) (parameter.relabel j) ht' he' hs' hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalParameterizedQuotientEdgeChecker InternalParameterizedQuotientEdgeCheckerSyntaxProof
open InternalParameterizedQuotientEdgeCheckerNormalizedProof InternalParameterizedQuotientEdgeCheckerTypedProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Three actual original selector outputs are obtained by internal Program
totality and eliminated through the same derivation context. -/
theorem selectorCases (certificate : OTerm α) (psi : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (s t k : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (selectors (certificate.relabel j) s t k)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply queryCases (![source,target,step] : Fin 3 → Program 1)
    (Fin.cons certificate Fin.elim0) psi
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  exact next β j Delta (ys 0) (ys 1) (ys 2) hj
    (andIntro (hq 0) (andIntro (hq 1) (hq 2)))

theorem normalizedCases (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (s t k : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (selectors (certificate.relabel j) s t k)) →
      Nonempty (Derivation body Delta
        (normalizedRequirements data oldStep (x.relabel j) (y.relabel j)
          s t k (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply selectorCases certificate psi
  intro β j Delta s t k hj hf
  have h' := renameInto h j Delta hj
  rw [coreAcceptedRename] at h'
  exact next β j Delta s t k hj hf
    (normalizedRecover data oldStep (x.relabel j) (y.relabel j) (certificate.relabel j)
      s t k (parameter.relabel j) hf h')

/-- The final selected edge exposes the same raw W and both N witnesses;
its outer typed guards introduce no extra certificate field. -/
theorem acceptedCases (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (accepted data oldStep x y certificate parameter)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (s t k : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (selectors (certificate.relabel j) s t k)) →
      Nonempty (Derivation body Delta
        (normalizedRequirements data oldStep (x.relabel j) (y.relabel j)
          s t k (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) :=
  normalizedCases data oldStep x y certificate parameter psi
    (acceptedCore data oldStep x y certificate parameter h) next

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerWitnessProof

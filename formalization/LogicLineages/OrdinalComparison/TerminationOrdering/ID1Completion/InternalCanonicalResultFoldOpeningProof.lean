module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalResultFoldOpening InternalCanonicalResultFoldOpeningTargets
open InternalCanonicalResultFoldOpeningQueryProof InternalCanonicalResultFoldOpeningSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Existentially introduce only outputs of the ten original finite Programs.
Every recovered opening fact is then proved by the checked query argument. -/
theorem openingCases (V member : Program 1) (parent : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (openingAccepted V member parent)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (payload middle children arrow d e fp ap fn arg : OrdinaryArithmetic.Term β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (openingWitnesses V member (parent.relabel j)
        payload middle children arrow d e fp ap fn arg)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply queryCases queries (Fin.cons parent Fin.elim0) psi
  intro β j ys Delta hj hq
  have h' := InternalGraphCompositionFunctionalityProof.renameInto h j Delta hj
  simp only [openingAcceptedRename] at h'
  have hq' : ∀ i, Nonempty (Derivation body Delta
      (graph1 (queries i) (ys i) (parent.relabel j))) := by
    intro i
    simpa only [consTermRename,emptyRename] using hq i
  exact step β j Delta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) hj
    (atQueries V member (parent.relabel j) ys h' hq')

/-- Actual full opening acceptance supplies all ten existential witnesses. -/
theorem openingRecover (V member : Program 1) (parent : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (openingAccepted V member parent))) :
    Nonempty (Derivation body Gamma (opened V member parent)) := by
  apply openingCases V member parent (opened V member parent) h
  intro β j Delta payload middle children arrow d e fp ap fn arg _ hw
  simpa only [openedRename] using
    openedIntro V member (parent.relabel j) payload middle children arrow d e fp ap fn arg hw

/-- The converse uses the same internal witnesses, without semantic decoding. -/
theorem openedAccept (V member : Program 1) (parent : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (opened V member parent))) :
    Nonempty (Derivation body Gamma (openingAccepted V member parent)) := by
  apply openedCases V member parent (openingAccepted V member parent) h
  intro β j Delta payload middle children arrow d e fp ap fn arg _ hw
  simpa only [openingAcceptedRename] using
    acceptWitnesses V member (parent.relabel j) payload middle children arrow d e fp ap fn arg hw

theorem actualOriginalCanonicalFoldOpeningFactorization :
    ActualOriginalCanonicalFoldOpeningFactorization := by
  intro body V member α Gamma parent
  obtain ⟨hf⟩ := openingRecover (body := body)
    (Gamma := openingAccepted V member parent :: Gamma) V member parent
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := openedAccept (body := body)
    (Gamma := opened V member parent :: Gamma) V member parent
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalCanonicalFoldOpeningContinuation :
    ActualOriginalCanonicalFoldOpeningContinuation := by
  intro body V member α Gamma parent psi h step
  exact openingCases V member parent psi h step

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningProof

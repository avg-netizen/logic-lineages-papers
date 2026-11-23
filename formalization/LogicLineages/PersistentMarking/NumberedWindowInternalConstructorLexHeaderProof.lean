module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLexHeaderTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLexHeaderProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAt)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalConstructorLexHeaderTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem omegaCase (raw : OTerm α) (goal : Formula α)
    (hit : D B Γ (headerAt 4 2 raw))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head base : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      OmegaFields B Δ (raw.relabel j) head base → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  apply exact_OpenCoverHeaderFields 4 2 B α Γ raw goal hit
  intro β j Δ fs keep len reports owner
  rcases fs with _ | ⟨head, _ | ⟨base, _ | ⟨more,rest⟩⟩⟩ <;> try simp at len
  exact next β j Δ head base keep ⟨owner,reports.1,reports.2.1⟩

private theorem finiteCase (raw : OTerm α) (goal : Formula α)
    (hit : D B Γ (headerAt 5 5 raw))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (head ty label base extras : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      FiniteFields B Δ (raw.relabel j) head ty label base extras → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  apply exact_OpenCoverHeaderFields 5 5 B α Γ raw goal hit
  intro β j Δ fs keep len reports owner
  rcases fs with _ | ⟨head, _ | ⟨ty, _ | ⟨label, _ | ⟨base, _ | ⟨extras, _ | ⟨more,rest⟩⟩⟩⟩⟩⟩ <;>
    try simp at len
  exact next β j Δ head ty label base extras keep
    ⟨owner,reports.1,reports.2.1,reports.2.2.1,reports.2.2.2.1,reports.2.2.2.2.1⟩

theorem exact_OpenConstructorLexHeaderCases : ExactOpenConstructorLexHeaderCases := by
  intro B α Γ raw goal headers omega finite
  let O := headerAt 4 2 raw
  let F := headerAt 5 5 raw
  have omega' : D B Γ (O.imp goal) := by
    have h : D B (O :: Γ) O := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨p⟩ := omegaCase raw goal h (fun β j Δ h b keep =>
      omega β j Δ h b (fun q hq => keep q (List.mem_cons_of_mem _ hq)))
    exact ⟨Derivation.implicationIntroduction p⟩
  have finite' : D B Γ (F.imp goal) := by
    have h : D B (F :: Γ) F := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨p⟩ := finiteCase raw goal h (fun β j Δ h ty n b es keep =>
      finite β j Δ h ty n b es (fun q hq => keep q (List.mem_cons_of_mem _ hq)))
    exact ⟨Derivation.implicationIntroduction p⟩
  obtain ⟨hp⟩ := headers
  obtain ⟨op⟩ := omega'
  obtain ⟨fp⟩ := finite'
  exact ⟨disjunctionElimination hp op fp⟩

#print axioms exact_OpenConstructorLexHeaderCases

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLexHeaderProof

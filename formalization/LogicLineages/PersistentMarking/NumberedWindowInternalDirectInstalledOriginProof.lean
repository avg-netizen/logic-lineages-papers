module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectProjectedCertSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOrigin
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInstalledOriginTargets
open NumberedWindowInternalDirectInstalledOriginSyntaxProof (targetMember addReportHyp)
open NumberedWindowInternalDirectCoreInstalledCertificateProof (exact_InstalledCertificateSharedTape)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectProjectedCert (exactProjectedCert)
open NumberedWindowInternalDirectProjectedCertSyntaxProof (renameShared)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser keepThrough)
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalDirectTargetMapOriginTargets (originRow)

private theorem onShared (count : Program 2) (r : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (src dst kept removed inserted s t k d a p sk tp key : OTerm α) (goal : Formula α)
    (shared : Reports count count r B Γ src dst kept removed inserted s t k d a p sk tp)
    (joined : Nonempty (Derivation B Γ (memberGraph tp key)))
    (stay : Nonempty (Derivation B (memberGraph k key :: Γ) goal))
    (replace : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (row dom cert : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Reports count count r B Δ (src.relabel ρ) (dst.relabel ρ) (kept.relabel ρ)
        (removed.relabel ρ) (inserted.relabel ρ) (s.relabel ρ) (t.relabel ρ) (k.relabel ρ)
        (d.relabel ρ) (a.relabel ρ) (p.relabel ρ) (sk.relabel ρ) (tp.relabel ρ) →
      Nonempty (Derivation B Δ (originRow (a.relabel ρ) (key.relabel ρ) row)) →
      NumberedWindowInternalDirectInsertedRowCasesTargets.Reports r B Δ
        (removed.relabel ρ) row (d.relabel ρ) (key.relabel ρ) dom cert →
      Nonempty (Derivation B Δ (goal.relabel ρ))) :
    Nonempty (Derivation B Γ goal) := by
  obtain ⟨split⟩ := exact_OpenScratchAppendOrigin B α Γ k p tp key shared.targetAppend joined
  let P := memberGraph p key
  have move : Nonempty (Derivation B (P :: Γ) goal) := by
    have saved := addReportHyp count r src dst kept removed inserted s t k d a p sk tp shared P
    apply exactProjectedCert count count r B α (P :: Γ) src dst kept removed inserted
      s t k d a p sk tp key goal saved ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β ρ Δ row dom cert retain own fields
    have keptAll : ∀ f ∈ Γ, f.relabel ρ ∈ Δ :=
      fun f hf => retain f (List.mem_cons_of_mem P hf)
    exact replace β ρ Δ row dom cert keptAll
      (renameShared count count r src dst kept removed inserted s t k d a p sk tp shared ρ keptAll)
      own fields
  obtain ⟨left⟩ := stay
  obtain ⟨right⟩ := move
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction left)
    (Derivation.implicationIntroduction right)⟩

theorem exactInstalledSuccessorOrigin : ExactInstalledSuccessorOrigin := by
  intro i j r count c α Γ src w dst known key goal
  dsimp only
  intro law odd knownReport knownMember keptCase replacementCase
  let B := sourceBody (data i j r (dCore i r count)) c
  apply exact_InstalledCertificateSharedTape i j r count c α Γ src w dst goal odd
  intro β ρ Δ kept removed inserted s t k d a p sk tp keep _ _ _ shared
  let S := src.relabel ρ
  let T := dst.relabel ρ
  let K := key.relabel ρ
  have parsed := renameParser dst known knownReport ρ Δ keep
  have member := renameInto knownMember ρ Δ keep
  rw [graphRename] at member
  have target := targetMember T (known.relabel ρ) t K parsed shared.targetParsed member
  have appended := law β Δ t tp K shared.targetObserved target
  apply onShared count r B β Δ S T kept removed inserted s t k d a p sk tp K (goal.relabel ρ)
    shared appended
  · let H := memberGraph k K
    exact keptCase β ρ (H :: Δ) kept removed inserted s t k d a p sk tp
      (fun f hf => List.mem_cons_of_mem H (keep f hf))
      (addReportHyp count r S T kept removed inserted s t k d a p sk tp shared H)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro γ m Ω row dom cert retain saved origin fields
    let ρ' := m ∘ ρ
    rw [formulaRelabelComposition]
    apply replacementCase γ ρ' Ω (kept.relabel m) (removed.relabel m) (inserted.relabel m)
      (s.relabel m) (t.relabel m) (k.relabel m) (d.relabel m) (a.relabel m) (p.relabel m)
      (sk.relabel m) (tp.relabel m) row dom cert (keepThrough ρ m keep retain)
    · simpa only [S,T,ρ',Term.relabel_relabel] using saved
    · simpa only [K,ρ',Term.relabel_relabel] using origin
    · simpa only [K,ρ',Term.relabel_relabel] using fields

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInstalledOrigin

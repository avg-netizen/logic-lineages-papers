module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport valueUnique zeroSuccessorCases equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc)
open ID1Completion.InternalTagArithmeticSupportProof (zeroNeSuc cancelSuc)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalFreshProbeTargets
open NumberedWindowInternalFreshProbeSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Case analysis on the actual output of any original Program. In the
successor branch the predecessor is a real object eigenvariable. -/
theorem optionGraphCases {n : Nat} (p : Program n) (xs : Fin n → OTerm α) (ψ : Formula α)
    (missing : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph p z (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Δ (ψ.relabel j)))
    (present : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph p (suc u) (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Δ (ψ.relabel j))) :
    Nonempty (Derivation body Γ ψ) := by
  apply programCases p xs ψ
  intro β j Δ r hj hr
  apply zeroSuccessorCases Δ r (ψ.relabel j)
  · obtain ⟨dr⟩ := hr
    have h0 := outputTransport p r z (fun i => (xs i).relabel j)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp dr _⟩
    exact missing β j _ (fun f hf => List.mem_cons_of_mem _ (hj f hf)) h0
  · intro γ k Θ u hk he
    have ht := renameInto hr k Θ hk
    rw [programRename] at ht
    have hsucc := outputTransport p (r.relabel k) (suc u)
      (fun i => ((xs i).relabel j).relabel k) he ht
    simp only [Term.relabel_relabel] at hsucc
    rw [formulaRelabelComposition]
    apply present γ (k ∘ j) Θ u _ hsucc
    intro f hf
    simpa only [formulaRelabelComposition] using hk (f.relabel j) (hj f hf)

theorem outputCases : FreshProbeOutputCases := by
  intro body a α Γ q
  apply optionGraphCases a ![q] (rejectedAt a q ⊔ chosenAt a q)
  · intro β j Δ _ hz
    rw [splitRename]
    rw [unaryRename] at hz
    obtain ⟨h⟩ := hz
    exact ⟨orLeft h⟩
  · intro β j Δ u _ hs
    rw [splitRename]
    rw [unaryRename] at hs
    obtain ⟨h⟩ := hs
    apply Nonempty.intro
    apply orRight
    unfold chosenAt
    apply Derivation.existentialIntroduction (emb u)
    rw [freshInstantiate]
    exact h

theorem rejectedExcludes : FreshProbeRejectedExcludes := by
  intro body a α Γ q u
  have hz : Derivation body (freshAt a q u :: rejectedAt a q :: Γ) (rejectedAt a q) :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hs : Derivation body (freshAt a q u :: rejectedAt a q :: Γ) (freshAt a q u) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨he⟩ := valueUnique a z (suc u) ![q] ⟨hz⟩ ⟨hs⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction (zeroNeSuc he))⟩

theorem unique : FreshProbeUnique := by
  intro body a α Γ q u v
  let A := freshAt a q u ⊓ freshAt a q v
  have h : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨he⟩ := valueUnique a (suc u) (suc v) ![q]
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction (by simpa only [equalEqn] using cancelSuc he)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof

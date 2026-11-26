module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules ID1Completion.InternalAccessibilityRulesProof
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding liftBind varBind)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBinderTransportProof (arithmeticRename)
open ID1Completion.InternalSliceInductionSyntaxProof (anyFormulaSubstRelabel)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists membershipSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open NumberedWindowInternalCertifiedUnionStepProof (Pr unionGraph HeldOuter HeldInner)
open NumberedWindowInternalCertifiedUnionInnerSyntaxProof
open NumberedWindowInternalCertifiedUnionInnerInductionProof (exact_ActualInnerLowerState)

abbrev Preserves {α β : Type} (Γ : List (Formula α)) (j : α → β)
    (Δ : List (Formula β)) : Prop :=
  ∀ f ∈ Γ, f.relabel j ∈ Δ

theorem freshKeeps {α : Type} (Γ : List (Formula α)) (fresh : Formula (α ⊕ Fin 1)) :
    Preserves Γ Sum.inl (fresh :: Γ.map weaken) := by
  intro f hf
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)

theorem keepsComp {α β γ : Type} (Γ : List (Formula α)) (Δ : List (Formula β))
    (Ξ : List (Formula γ)) (j : α → β) (k : β → γ)
    (hj : Preserves Γ j Δ) (hk : Preserves Δ k Ξ) : Preserves Γ (k ∘ j) Ξ := by
  intro f hf
  rw [← formulaRelabelComposition j k f]
  exact hk _ (hj f hf)

theorem oddCarrierRename {α β : Type} (data : Data) (c : Nat) (a : OTerm α) (j : α → β) :
    (carrier data true c a).relabel j = carrier data true c (a.relabel j) := by
  unfold carrier
  rw [← arithmeticRename,anyFormulaSubstRelabel]
  have tape : (fun i : Fin 2 => ((![numeral c,a] : Fin 2 → OTerm α) i).relabel j) =
      ![numeral c,a.relabel j] := by
    funext i
    exact Fin.cases (ID1Completion.GuardedSourceSyntaxProof.numeralRename c j)
      (Fin.cases rfl (fun q => Fin.elim0 q)) i
  rw [tape]

theorem unionGraphRename {α β : Type} (count : Program 2) (a b u : OTerm α)
    (j : α → β) :
    (unionGraph count a b u).relabel j =
      unionGraph count (a.relabel j) (b.relabel j) (u.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (unionGraph count a b u).subst (fun i => emb (.var (j i))) = _
  rw [unionGraphSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem retainOuter {α β : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (Δ : List (Formula β)) (a : OTerm α) (j : α → β)
    (keep : Preserves Γ j Δ) (outer : HeldOuter data c count Γ a) :
    HeldOuter data c count Δ (a.relabel j) := by
  intro γ k Ξ a' b' u' kept strict right joined
  apply outer γ (k ∘ j) Ξ a' b' u' (keepsComp Γ Δ Ξ j k keep kept)
  · simpa only [Term.relabel_relabel] using strict
  · exact right
  · exact joined

theorem consequenceApply {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (a b u : OTerm α) :
    Pr data c Γ (consequence count a b) →
    Pr data c Γ (unionGraph count a b u) →
    Pr data c Γ (membership true u) := by
  rintro ⟨conseq⟩ ⟨joined⟩
  have h := Derivation.universalElimination (emb u) conseq
  simp only [instantiate,bindEmbedding,impSubst,unionGraphSubst,membershipSubst,liftBind,varBind] at h
  exact ⟨Derivation.implicationElimination h joined⟩

theorem heldInnerOfActualLower {α : Type} (data : Data) (c : Nat) (count : Program 2)
    (Γ : List (Formula α)) (a b : OTerm α)
    (lower : Pr data c Γ (innerLower data c count a b)) :
    HeldInner data c count Γ a b := by
  intro β j Δ b' u' keep strict joined
  have moved := renameInto lower j Δ keep
  rw [innerLowerRename] at moved
  obtain ⟨h⟩ := exact_ActualInnerLowerState data c count Δ (a.relabel j) (b.relabel j) b' moved strict
  exact consequenceApply data c count Δ (a.relabel j) b' u'
    ⟨Derivation.conjunctionRight h⟩ joined

/-- Elimination of the actual existential odd edge into a fresh original
certificate, in the current natural-deduction theory. -/
theorem oddCertificateCases {α : Type} (data : Data) (c : Nat) (Γ : List (Formula α))
    (u v : OTerm α) (goal : Formula α)
    (step : Pr data c Γ (edge data true c u v))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w : OTerm β),
      Preserves Γ j Δ →
      Pr data c Δ (certificate data true c (u.relabel j) (v.relabel j) w) →
      Pr data c Δ (goal.relabel j)) :
    Pr data c Γ goal := by
  obtain ⟨d⟩ := step
  rw [edgeExists] at d
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := certificate data true c (u.relabel Sum.inl) (v.relabel Sum.inl) w
  obtain ⟨h⟩ := next (α ⊕ Fin 1) Sum.inl (P :: Γ.map weaken) w (freshKeeps Γ P)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination d h⟩

/-- An open-premise form of the actual J introduction rule. -/
theorem oddIntroduction {α : Type} (data : Data) (c : Nat) (Γ : List (Formula α))
    (u : OTerm α) (typed : Pr data c Γ (carrier data true c u))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (v : OTerm β),
      Preserves Γ j Δ →
      Pr data c Δ (edge data true c (u.relabel j) v) →
      Pr data c Δ (membership true v)) :
    Pr data c Γ (membership true u) := by
  apply actualOriginalAccessibilityIntroduction data true c α Γ u typed
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := edge data true c (u.relabel Sum.inl) v
  obtain ⟨h⟩ := next (α ⊕ Fin 1) Sum.inl (P :: Γ.map weaken) v (freshKeeps Γ P)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction h)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof

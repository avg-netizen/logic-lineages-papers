module

public import LogicLineages.OrdinalComparison.SourceSubstitutionSupportTargets
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceSubstitutionSupportProof
open SourceTypeSupport SourceSubstitutionSupportTargets

theorem actualSubstitutionSupport : ActualSubstitutionSupport := by
  intro Symbol arity Γ Δ τ t
  induction t generalizing Δ with
  | var v => intro s K ht hs; exact hs _ v
  | app f a ihf iha =>
    intro s K ht hs
    obtain ⟨hroot, hargs⟩ := Finset.union_subset_iff.mp ht
    obtain ⟨hf, ha⟩ := Finset.union_subset_iff.mp hargs
    exact Finset.union_subset_iff.mpr ⟨hroot, Finset.union_subset_iff.mpr
      ⟨ihf Δ s K hf hs, iha Δ s K ha hs⟩⟩
  | lam body ih =>
    intro s K ht hs
    obtain ⟨hroot, hbody⟩ := Finset.union_subset_iff.mp ht
    refine Finset.union_subset_iff.mpr ⟨hroot, ih _ s.lift K hbody ?_⟩
    intro σ v
    cases v with
    | here =>
      simpa only [Substitution.lift, typeSupport, Finset.union_empty] using
        ((SourceTypeSupportProof.literalBinderSupport Symbol arity _ _ _ body).2.1.trans ht)
    | there v =>
      change typeSupport ((s v).rename (Renaming.weaken Δ _)) ⊆ K
      rw [(SourceTypeSupportProof.supportDepthRenaming Symbol arity _ _ _ (s v) _).1]
      exact hs _ v
  | zeroC => intro s K ht hs; exact ht
  | succC => intro s K ht hs; exact ht
  | caseC τ => intro s K ht hs; exact ht
  | recC τ => intro s K ht hs; exact ht
  | ranked head args ih =>
    intro s K ht hs
    obtain ⟨hroot, hargs⟩ := Finset.union_subset_iff.mp ht
    refine Finset.union_subset_iff.mpr ⟨hroot, ?_⟩
    intro σ hσ
    obtain ⟨i, hi, hmem⟩ := Finset.mem_biUnion.mp hσ
    exact ih i Δ s K (fun υ hυ => hargs (Finset.mem_biUnion.mpr ⟨i, hi, hυ⟩)) hs hmem

theorem actualSubstitutionDepth : ActualSubstitutionDepth := by
  intro Symbol arity Γ Δ τ t
  induction t generalizing Δ with
  | var v =>
    intro s L hs
    exact ⟨Nat.zero_le _, by simpa only [Term.substitute, lambdaDepth, Nat.zero_add] using hs _ v⟩
  | app f a ihf iha =>
    intro s L hs
    have hf := ihf Δ s L hs
    have ha := iha Δ s L hs
    simp only [Term.substitute, lambdaDepth]
    omega
  | lam body ih =>
    intro s L hs
    have hb := ih _ s.lift L (by
      intro σ v
      cases v with
      | here => exact Nat.zero_le _
      | there v =>
        change lambdaDepth ((s v).rename (Renaming.weaken Δ _)) ≤ L
        rw [(SourceTypeSupportProof.supportDepthRenaming Symbol arity _ _ _ (s v) _).2]
        exact hs _ v)
    simp only [Term.substitute, lambdaDepth]
    constructor
    · exact Nat.add_le_add_right hb.1 1
    · exact (Nat.add_le_add_right hb.2 1).trans_eq (by omega)
  | zeroC => intro s L hs; simp [Term.substitute, lambdaDepth]
  | succC => intro s L hs; simp [Term.substitute, lambdaDepth]
  | caseC τ => intro s L hs; simp [Term.substitute, lambdaDepth]
  | recC τ => intro s L hs; simp [Term.substitute, lambdaDepth]
  | ranked head args ih =>
    intro s L hs
    constructor
    · apply Finset.sup_le
      intro i hi
      exact (ih i Δ s L hs).1.trans (Finset.le_sup (f := fun j => lambdaDepth ((args j).substitute s)) hi)
    · apply Finset.sup_le
      intro i hi
      exact (ih i Δ s L hs).2.trans (Nat.add_le_add_right
        (Finset.le_sup (f := fun j => lambdaDepth (args j)) hi) L)

private theorem lift_variables {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    {σ : Ty} (ρ : Renaming Γ Δ) :
    @Substitution.lift Symbol arity Γ Δ σ
      (fun {υ : Ty} (v : Variable Γ υ) => (Term.var (ρ v) : Term Symbol arity Δ υ)) =
      (fun {υ : Ty} (v : Variable (σ :: Γ) υ) =>
        (Term.var (ρ.lift v) : Term Symbol arity (σ :: Δ) υ)) := by
  funext υ v
  cases v <;> rfl

theorem variableSubstitutionRenaming : VariableSubstitutionRenaming := by
  intro Symbol arity Γ Δ τ t ρ
  induction t generalizing Δ with
  | var v => rfl
  | app f a ihf iha => simp only [Term.substitute, Term.rename, ihf Δ ρ, iha Δ ρ]
  | lam body ih =>
    rw [Term.substitute, lift_variables, ih _ ρ.lift]
    rfl
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked head args ih =>
    change Term.ranked head (fun i => (args i).substitute (fun v => Term.var (ρ v))) =
      Term.ranked head (fun i => (args i).rename ρ)
    congr 1
    funext i
    exact ih i Δ ρ

theorem typedBodyOpeningBudget : TypedBodyOpeningBudget := by
  intro Symbol arity Γ Δ σ τ body ρ
  obtain ⟨hs, hd⟩ := SourceTypeSupportProof.supportDepthRenaming Symbol arity _ _ _ body ρ
  rw [hs, hd]
  refine ⟨(SourceTypeSupportProof.literalBinderSupport Symbol arity Γ σ τ body).2.2.1, rfl, ?_⟩
  intro used B h
  change used + (lambdaDepth body + 1) ≤ B at h
  omega

end LogicLineages.OrdinalComparison.Source.SourceSubstitutionSupportProof

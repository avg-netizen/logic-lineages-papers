module

public import LogicLineages.OrdinalComparison.SourceTypeSupportTargets
public import LogicLineages.OrdinalComparison.SourceTypesProofs

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypeSupportProof
open SourceTypeSupport SourceTypeSupportTargets

private theorem root_subset {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : τ.subtypes.toFinset ⊆ typeSupport t := by
  cases t <;> exact Finset.subset_union_left

theorem actualResultSupport : ActualResultSupport := by
  intro Symbol arity Γ τ t
  exact root_subset t (List.mem_toFinset.mpr (Ty.mem_subtypes_self τ))

private def Closed (s : Finset Ty) : Prop :=
  ∀ σ ∈ s, ∀ υ ∈ σ.subtypes, υ ∈ s

private theorem closed_subtypes (τ : Ty) : Closed τ.subtypes.toFinset := by
  intro σ hσ υ hυ
  exact List.mem_toFinset.mpr (typeSubexpressionClosure τ σ (List.mem_toFinset.mp hσ) υ hυ)

private theorem closed_union {s t : Finset Ty} (hs : Closed s) (ht : Closed t) : Closed (s ∪ t) := by
  intro σ hσ υ hυ
  rcases Finset.mem_union.mp hσ with hσ | hσ
  · exact Finset.mem_union_left _ (hs σ hσ υ hυ)
  · exact Finset.mem_union_right _ (ht σ hσ υ hυ)

private theorem closed_empty : Closed ∅ := by simp [Closed]

private theorem support_closed {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : Closed (typeSupport t) := by
  induction t with
  | var v => exact closed_union (closed_subtypes _) closed_empty
  | app f a ihf iha => exact closed_union (closed_subtypes _) (closed_union ihf iha)
  | lam body ih => exact closed_union (closed_subtypes _) ih
  | zeroC => exact closed_union (closed_subtypes _) closed_empty
  | succC => exact closed_union (closed_subtypes _) closed_empty
  | caseC τ => exact closed_union (closed_subtypes _) closed_empty
  | recC τ => exact closed_union (closed_subtypes _) closed_empty
  | ranked s args ih =>
    apply closed_union (closed_subtypes _)
    intro σ hσ υ hυ
    obtain ⟨i, hi, hmem⟩ := Finset.mem_biUnion.mp hσ
    exact Finset.mem_biUnion.mpr ⟨i, hi, ih i σ hmem υ hυ⟩

theorem subtypeClosedSupport : SubtypeClosedSupport := by
  intro Symbol arity Γ τ t
  exact support_closed t

theorem supportDepthRenaming : SupportDepthRenaming := by
  intro Symbol arity Γ Δ τ t ρ
  induction t generalizing Δ with
  | var v => exact ⟨rfl, rfl⟩
  | app f a ihf iha =>
    have hf := ihf Δ ρ
    have ha := iha Δ ρ
    simp only [Term.rename, typeSupport, lambdaDepth, hf.1, hf.2, ha.1, ha.2, and_self]
  | lam body ih =>
    have hb := ih _ ρ.lift
    simp only [Term.rename, typeSupport, lambdaDepth, hb.1, hb.2, and_self]
  | zeroC => exact ⟨rfl, rfl⟩
  | succC => exact ⟨rfl, rfl⟩
  | caseC τ => exact ⟨rfl, rfl⟩
  | recC τ => exact ⟨rfl, rfl⟩
  | ranked s args ih =>
    have hs : (fun i => typeSupport ((args i).rename ρ)) = (fun i => typeSupport (args i)) :=
      funext fun i => (ih i Δ ρ).1
    have hd : (fun i => lambdaDepth ((args i).rename ρ)) = (fun i => lambdaDepth (args i)) :=
      funext fun i => (ih i Δ ρ).2
    simp only [Term.rename, typeSupport, lambdaDepth, hs, hd, and_self]

theorem literalBinderSupport : LiteralBinderSupport := by
  intro Symbol arity Γ σ τ body
  refine ⟨rfl, ?_, Finset.subset_union_right, rfl⟩
  intro υ hυ
  apply root_subset (Term.lam body)
  apply List.mem_toFinset.mpr
  simp only [Ty.subtypes, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (List.mem_toFinset.mp hυ))

theorem literalRankedSupport : LiteralRankedSupport := by
  intro Symbol arity Γ s args
  simp [typeSupport, Ty.subtypes, lambdaDepth]

end LogicLineages.OrdinalComparison.Source.SourceTypeSupportProof

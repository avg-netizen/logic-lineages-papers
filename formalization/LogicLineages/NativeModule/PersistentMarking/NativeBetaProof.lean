module

public import LogicLineages.NativeModule.PersistentMarking.NativeBetaSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeBetaProof
open Spine NameBridge NativeReduction NativeTypingProof NativeBetaSupport TypeSupport Grafting

mutual
 theorem freeSupport (σ : Ty) (x : Nat) (q : Expr) (hf : freeOccurs (σ,x) q = true)
    (ρ : Ty) (hρ : ρ ∈ subtypes σ) : ρ ∈ support q := by
  cases q with
  | free δ y =>
    have he : (σ,x) = (δ,y) := by simpa only [freeOccurs,decide_eq_true_eq] using hf
    have ht : σ = δ := congrArg Prod.fst he
    subst δ
    exact hρ
  | bound δ i => simp [freeOccurs] at hf
  | lam δ q =>
    simp only [support,List.mem_append]
    exact Or.inr (freeSupport σ x q hf ρ hρ)
  | head f qs =>
    simp only [support,List.mem_append]
    exact Or.inr (freeArgsSupport σ x qs hf ρ hρ)
  | marked f τ qs es =>
    have hh : freeOccursArgs (σ,x) qs = true ∨ freeOccursArgs (σ,x) es = true := by
      simpa only [freeOccurs,Bool.or_eq_true] using hf
    simp only [support,List.mem_append]
    rcases hh with hh | hh
    · exact Or.inl (Or.inr (freeArgsSupport σ x qs hh ρ hρ))
    · exact Or.inr (freeArgsSupport σ x es hh ρ hρ)
 termination_by sizeOf q
 theorem freeArgsSupport (σ : Ty) (x : Nat) (qs : Args) (hf : freeOccursArgs (σ,x) qs = true)
    (ρ : Ty) (hρ : ρ ∈ subtypes σ) : ρ ∈ supportArgs qs := by
  cases qs with
  | nil => simp [freeOccursArgs] at hf
  | cons q qs =>
    have hh : freeOccurs (σ,x) q = true ∨ freeOccursArgs (σ,x) qs = true := by
      simpa only [freeOccursArgs,Bool.or_eq_true] using hf
    simp only [supportArgs,List.mem_append]
    rcases hh with hh | hh
    · exact Or.inl (freeSupport σ x q hh ρ hρ)
    · exact Or.inr (freeArgsSupport σ x qs hh ρ hρ)
 termination_by sizeOf qs
end

theorem beta : NativeOrientationTargets.Beta := by
  intro S σ τ body B hb hv ho hB hoB
  have hLam : PaperTerm S (.lam σ body) (.arrow σ τ) := ⟨.lam hb,hv⟩
  have hsource := appPaper S σ τ (.lam σ body) B hLam hB
  let own := fun ρ => Expr.marked (.app σ τ) ρ (.cons (.lam σ body) (.cons B .nil)) .nil
  have hown : ∀ ρ, PaperTerm S (own ρ) ρ := fun ρ => markedAppPaper S σ τ ρ (.lam σ body) B .nil hLam hB .nil True.intro
  have hselected : Weak S (own σ) B := secondSelect S σ τ (.lam σ body) B .nil hLam hB hoB .nil True.intro
  obtain ⟨x,hfresh,_⟩ := OpeningFoundationProof.freshOpeningExists σ body body
  have htemplate := ElementarySupportProof.openingPaper S σ τ x body hLam
  have hotemplate := ElementarySupportProof.openOrdinary σ x 0 body ho
  have hgraft := GraftingProof.templateGrafting S (openBody σ x body) τ σ x (own σ) B
    htemplate hotemplate (hown σ) hB hselected
  rw [realize σ x (own σ) body hfresh,realize σ x B body hfresh] at hgraft
  obtain ⟨htree⟩ := AuxiliaryEmbeddingProof.embedWeak S _ _ hgraft
  have hfacts := ExtendedEndpointProof.weakFacts htree
  have htarget : PaperTerm S (substitute (.cons B .nil) 0 body) τ :=
    ⟨SpineSubstitutionProof.parallelPreserves EmptyContext [σ] (.cons B .nil) body τ (.cons hB.1 .nil) hb,hfacts.2.1.2⟩
  have hotarget := ComparisonOrdinaryProof.weakOrdinary S _ _ hgraft
  have hcall : apply (.lam σ body) (ownerCopies (.app σ τ) (.cons (.lam σ body) (.cons B .nil)) .nil [σ]) =
      some (substitute (.cons (own σ) .nil) 0 body) := by
    simp [apply,applyAux,ownerCopies,own,Expr.type]
  have hw : Weak S (own τ) (substitute (.cons B .nil) 0 body) :=
    .select (domains := [σ]) (hown τ) htarget (Or.inl .here) hLam.1 hcall hgraft
  refine ⟨⟨τ,hsource,htarget,appOrdinary σ τ _ _ ho hoB,hotarget⟩,Strict.intro hsource htarget rfl hw,?_⟩
  have hm : StructuralStabilityTargets.OrdinaryMap S (singleMap σ x B) := by
    intro υ y
    by_cases he : (υ,y) = (σ,x)
    · have htype := congrArg Prod.fst he
      simp only at htype
      subst υ
      simpa only [singleMap,he,if_true] using And.intro hB hoB
    · simp only [singleMap,he,if_false]
      exact ⟨⟨.free,True.intro⟩,True.intro⟩
  have templateIncluded : Included (openBody σ x body) (app σ τ (.lam σ body) B) := by
    intro ρ h
    rw [openingSupportExact σ τ x body hb] at h
    apply leftIncluded σ τ (.lam σ body) B ρ
    simp only [support,List.mem_append]
    exact Or.inr h
  intro ρ h
  have hex := TypeSupportSubstitutionProof.exactSubstitution S (openBody σ x body) τ (singleMap σ x B)
    htemplate hotemplate hm ρ
  rw [realize σ x B body hfresh] at hex
  rcases hex.mp h with h | ⟨υ,y,hy,hi⟩
  · exact templateIncluded ρ h
  · by_cases he : (υ,y) = (σ,x)
    · have hiB : ρ ∈ support B := by simpa only [singleMap,he,if_true] using hi
      exact rightIncluded σ τ (.lam σ body) B ρ hiB
    · have hiυ : ρ ∈ subtypes υ := by simpa only [singleMap,he,if_false,support] using hi
      exact templateIncluded ρ (freeSupport υ y (openBody σ x body) hy ρ hiυ)
end LogicLineages.PersistentMarking.NativeBetaProof

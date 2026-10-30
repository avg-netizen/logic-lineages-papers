module

public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesTargets
public import LogicLineages.OrdinalComparison.SourceSubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFreeOccurrencesProof
open SourceTypeSupport SourceFreeOccurrences SourceFreeOccurrencesTargets

private theorem drop_rename {Γ Δ : List Ty} {σ : Ty} (ρ : Renaming Γ Δ)
    (v : PackedVariable (σ :: Γ)) :
    dropBound (renamePacked ρ.lift v) = (dropBound v).map (renamePacked ρ) := by
  rcases v with ⟨τ, v⟩
  cases v <;> rfl

theorem freeOccurrenceRenaming : FreeOccurrenceRenaming := by
  intro Symbol arity Γ Δ τ t ρ
  induction t generalizing Δ with
  | var v => rfl
  | app f a ihf iha => simp only [Term.rename, freeOccurrences, ihf Δ ρ, iha Δ ρ, List.map_append]
  | lam body ih =>
    simp only [Term.rename, freeOccurrences, ih _ ρ.lift, List.filterMap_map, List.map_filterMap]
    apply congrArg (fun f => (freeOccurrences body).filterMap f)
    funext v
    exact drop_rename ρ v
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked head args ih =>
    simp only [Term.rename, freeOccurrences, List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact ih i Δ ρ

theorem occurringVariableTypeSupport : OccurringVariableTypeSupport := by
  intro Symbol arity Γ τ t
  induction t with
  | var w =>
    intro v hv
    have he : v = ⟨_, w⟩ := List.mem_singleton.mp hv
    subst v
    exact SourceTypeSupportProof.actualResultSupport Symbol arity _ _ (.var w)
  | app f a ihf iha =>
    intro v hv
    apply Finset.mem_union_right
    rcases List.mem_append.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ihf v hv)
    · exact Finset.mem_union_right _ (iha v hv)
  | lam body ih =>
    intro v hv
    obtain ⟨w, hw, hdrop⟩ := List.mem_filterMap.mp hv
    rcases w with ⟨σ, w⟩
    cases w with
    | here => cases hdrop
    | there w =>
      have he : (⟨σ, w⟩ : PackedVariable _) = v := Option.some.inj hdrop
      subst v
      exact Finset.mem_union_right _ (ih ⟨σ, .there w⟩ hw)
  | zeroC => intro v hv; cases hv
  | succC => intro v hv; cases hv
  | caseC τ => intro v hv; cases hv
  | recC τ => intro v hv; cases hv
  | ranked head args ih =>
    intro v hv
    obtain ⟨l, hl, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hl
    subst l
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ih i v hv⟩)

theorem imageTypeSupportMembership : ImageTypeSupportMembership := by
  intro Symbol arity Γ Δ s vars τ
  induction vars with
  | nil => simp [imageTypeSupport]
  | cons v vars ih => simp [imageTypeSupport, ih]

private theorem image_append {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (s : Substitution Symbol arity Γ Δ) (a b : List (PackedVariable Γ)) :
    imageTypeSupport s (a ++ b) = imageTypeSupport s a ∪ imageTypeSupport s b := by
  induction a with
  | nil => simp [imageTypeSupport]
  | cons v a ih => simp [imageTypeSupport, ih, Finset.union_assoc]

private theorem image_flatten_ofFn {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (s : Substitution Symbol arity Γ Δ) (n : Nat) (f : Fin n → List (PackedVariable Γ)) :
    imageTypeSupport s (List.ofFn f).flatten = Finset.univ.biUnion (fun i => imageTypeSupport s (f i)) := by
  ext τ
  simp only [imageTypeSupportMembership Symbol arity Γ Δ s, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, hτ⟩
    obtain ⟨l, hl, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hl
    subst l
    exact ⟨i, v, hv, hτ⟩
  · rintro ⟨i, v, hv, hτ⟩
    exact ⟨v, List.mem_flatten.mpr ⟨f i, List.mem_ofFn.mpr ⟨i, rfl⟩, hv⟩, hτ⟩

private theorem root_subset {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : τ.subtypes.toFinset ⊆ typeSupport t := by
  intro σ hσ
  exact SourceTypeSupportProof.subtypeClosedSupport Symbol arity Γ τ t τ
    (SourceTypeSupportProof.actualResultSupport Symbol arity Γ τ t) σ (List.mem_toFinset.mp hσ)

private theorem image_lift {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {σ : Ty}
    (s : Substitution Symbol arity Γ Δ) (vars : List (PackedVariable (σ :: Γ)))
    (K : Finset Ty) (hK : σ.subtypes.toFinset ⊆ K) :
    K ∪ imageTypeSupport (Substitution.lift s) vars =
      K ∪ imageTypeSupport s (vars.filterMap dropBound) := by
  induction vars with
  | nil => rfl
  | cons v vars ih =>
    rcases v with ⟨τ, v⟩
    cases v with
    | here =>
      simp only [imageTypeSupport, Substitution.lift, typeSupport, Finset.union_empty,
        List.filterMap_cons, dropBound]
      rw [← Finset.union_assoc, Finset.union_eq_left.mpr hK]
      exact ih
    | there v =>
      have hs := (SourceTypeSupportProof.supportDepthRenaming Symbol arity _ _ _ (s v)
        (Renaming.weaken Δ σ)).1
      simp only [imageTypeSupport, Substitution.lift, hs, List.filterMap_cons, dropBound]
      calc
        K ∪ (typeSupport (s v) ∪ imageTypeSupport (Substitution.lift s) vars) =
            typeSupport (s v) ∪ (K ∪ imageTypeSupport (Substitution.lift s) vars) := by ac_rfl
        _ = typeSupport (s v) ∪ (K ∪ imageTypeSupport s (vars.filterMap dropBound)) := congrArg _ ih
        _ = K ∪ (typeSupport (s v) ∪ imageTypeSupport s (vars.filterMap dropBound)) := by ac_rfl

theorem exactTypeSupportSubstitution : ExactTypeSupportSubstitution := by
  intro Symbol arity Γ Δ τ t s
  induction t generalizing Δ with
  | var v =>
    simp only [Term.substitute, typeSupport, freeOccurrences, imageTypeSupport, Finset.union_empty]
    exact (Finset.union_eq_right.mpr (root_subset (s v))).symm
  | app f a ihf iha =>
    simp only [Term.substitute, typeSupport, freeOccurrences, ihf Δ s, iha Δ s, image_append]
    ac_rfl
  | lam body ih =>
    have hb := ih _ s.lift
    have hK := (SourceTypeSupportProof.literalBinderSupport Symbol arity _ _ _ body).2.1
    change typeSupport (Term.lam (body.substitute s.lift)) = _
    simp only [typeSupport, freeOccurrences, hb]
    rw [← Finset.union_assoc]
    exact image_lift s (freeOccurrences body) (typeSupport (Term.lam body)) hK
  | zeroC => simp [Term.substitute, typeSupport, freeOccurrences, imageTypeSupport]
  | succC => simp [Term.substitute, typeSupport, freeOccurrences, imageTypeSupport]
  | caseC τ => simp [Term.substitute, typeSupport, freeOccurrences, imageTypeSupport]
  | recC τ => simp [Term.substitute, typeSupport, freeOccurrences, imageTypeSupport]
  | ranked head args ih =>
    simp only [Term.substitute, typeSupport, freeOccurrences, image_flatten_ofFn]
    have he : (fun i => typeSupport ((args i).substitute s)) =
        (fun i => typeSupport (args i) ∪ imageTypeSupport s (freeOccurrences (args i))) :=
      funext fun i => ih i Δ s
    rw [he]
    ext υ
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, exists_or]
    tauto

private theorem drop_weaken {Γ : List Ty} {σ : Ty} (vars : List (PackedVariable Γ)) :
    (vars.map (renamePacked (Renaming.weaken Γ σ))).filterMap dropBound = vars := by
  induction vars with
  | nil => rfl
  | cons v vars ih => rcases v with ⟨τ, v⟩; simpa [renamePacked, Renaming.weaken, dropBound] using congrArg (⟨τ, v⟩ :: ·) ih

private theorem free_lift {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {σ : Ty}
    (s : Substitution Symbol arity Γ Δ) (vars : List (PackedVariable (σ :: Γ))) :
    (vars.flatMap (fun v => freeOccurrences (Substitution.lift s v.2))).filterMap dropBound =
      (vars.filterMap dropBound).flatMap (fun v => freeOccurrences (s v.2)) := by
  induction vars with
  | nil => rfl
  | cons v vars ih =>
    rcases v with ⟨τ, v⟩
    cases v with
    | here => simpa [Substitution.lift, freeOccurrences, dropBound] using ih
    | there v =>
      have hr := freeOccurrenceRenaming Symbol arity _ _ _ (s v) (Renaming.weaken Δ σ)
      change (freeOccurrences ((s v).rename (Renaming.weaken Δ σ)) ++
        vars.flatMap (fun w => freeOccurrences (Substitution.lift s w.2))).filterMap dropBound =
        freeOccurrences (s v) ++ (vars.filterMap dropBound).flatMap (fun w => freeOccurrences (s w.2))
      rw [List.filterMap_append, hr]
      exact congrArg₂ List.append (drop_weaken (σ := σ) (freeOccurrences (s v))) ih

private theorem flatMap_flatten {α β : Type} (l : List (List α)) (f : α → List β) :
    l.flatten.flatMap f = (l.map (fun xs => xs.flatMap f)).flatten := by
  induction l with
  | nil => rfl
  | cons xs l ih => simp [List.flatMap_append, ih]

theorem exactFreeOccurrenceSubstitution : ExactFreeOccurrenceSubstitution := by
  intro Symbol arity Γ Δ τ t s
  induction t generalizing Δ with
  | var v => simp [Term.substitute, freeOccurrences]
  | app f a ihf iha => simp only [Term.substitute, freeOccurrences, ihf Δ s, iha Δ s, List.flatMap_append]
  | lam body ih =>
    simp only [Term.substitute, freeOccurrences, ih _ s.lift]
    exact free_lift s (freeOccurrences body)
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked head args ih =>
    simp only [Term.substitute, freeOccurrences, flatMap_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact ih i Δ s

end LogicLineages.OrdinalComparison.Source.SourceFreeOccurrencesProof

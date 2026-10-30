module
public import LogicLineages.OrdinalComparison.SourceFiniteNamedSubstitutionTargets
public import LogicLineages.OrdinalComparison.SourceNamedSubstitutionProof
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteNamedSubstitutionProof
open SourceNamedSyntax SourceNamedSyntaxProof SourceNamedSubstitution SourceNamedSubstitutionProof
open SourceFiniteNamedSubstitution SourceFiniteNamedSubstitutionTargets SourceTypeSupport
open SourceFreeOccurrences SourceFreeOccurrencesProof

theorem finiteNamedEntryEquations : FiniteNamedEntryEquations := by
  constructor
  · intro Symbol arity Γ a rest
    simp [finiteEnvironment]
  constructor
  · intro Symbol arity Γ a rest x σ h hn
    simp only [finiteEnvironment, dif_neg hn]
  · intro Symbol arity Γ entries x σ h hm
    induction entries with
    | nil => rfl
    | cons a rest ih =>
      have hn : x ≠ a.name := fun e => hm a (by simp) e.symm
      simp only [finiteEnvironment, dif_neg hn]
      exact ih (fun b hb => hm b (List.mem_cons_of_mem _ hb))

theorem namedImageSupportMembership : NamedImageSupportMembership := by
  intro Symbol arity Γ Δ env vs τ
  induction vs with
  | nil => simp [namedImageSupport]
  | cons v vs ih =>
    rcases v with ⟨x, σ⟩
    by_cases h : lookup Γ x = some σ
    · simp [namedImageSupport, ih, h]
    · simp [namedImageSupport, ih, h]

private theorem image_calibration {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : Context}
    {τ : Ty} (t : NamedTerm Symbol arity Γ τ) (env : NamedEnvironment Symbol arity Γ Δ) :
    imageTypeSupport (kernelEnvironment env) (freeOccurrences (erase t)) =
      namedImageSupport env (namedOccurrences t) := by
  have he {v : PackedVariable (contextTypes Γ)}
      (h : lookup Γ (namePacked v).1 = some (namePacked v).2) :
      typeSupport (kernelEnvironment env v.2) =
        namedSupport (env (namePacked v).1 (namePacked v).2 h) := by
    change typeSupport (if hh : lookup Γ (variableName v.2) = some v.1 then
      erase (env (variableName v.2) v.1 hh) else canonicalInhabitant (contextTypes Δ) v.1) = _
    change lookup Γ (variableName v.2) = some v.1 at h
    rw [dif_pos h]
    exact namedSupportCalibration Symbol arity Δ _ _
  ext σ
  rw [imageTypeSupportMembership, namedImageSupportMembership]
  constructor
  · rintro ⟨v, hv, hσ⟩
    have hn : namePacked v ∈ namedOccurrences t := by
      rw [← namedOccurrenceCalibration Symbol arity Γ τ t]
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    have hl := namedOccurrenceTyping Symbol arity Γ τ t (namePacked v) hn
    exact ⟨namePacked v, hn, hl, (he hl) ▸ hσ⟩
  · rintro ⟨v, hv, hl, hσ⟩
    rw [← namedOccurrenceCalibration Symbol arity Γ τ t] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact ⟨w, hw, (he hl).symm ▸ hσ⟩

theorem actualNamedSupportSubstitution : ActualNamedSupportSubstitution := by
  intro Symbol arity Γ Δ τ t env
  calc
    namedSupport (namedSubstitute t env) = typeSupport (erase (namedSubstitute t env)) :=
      (namedSupportCalibration Symbol arity Δ τ _).symm
    _ = typeSupport ((erase t).substitute (kernelEnvironment env)) :=
      congrArg typeSupport (actualNamedSubstitutionErasure Symbol arity Γ Δ τ t env)
    _ = typeSupport (erase t) ∪ imageTypeSupport (kernelEnvironment env) (freeOccurrences (erase t)) :=
      exactTypeSupportSubstitution Symbol arity (contextTypes Γ) (contextTypes Δ) τ (erase t) _
    _ = namedSupport t ∪ namedImageSupport env (namedOccurrences t) :=
      congrArg₂ (· ∪ ·) (namedSupportCalibration Symbol arity Γ τ t) (image_calibration t env)

theorem fullFiniteNamedSupportSubstitution : FullFiniteNamedSupportSubstitution := by
  intro Symbol arity Γ τ t entries
  exact actualNamedSupportSubstitution Symbol arity Γ Γ τ t (finiteEnvironment entries)

end LogicLineages.OrdinalComparison.Source.SourceFiniteNamedSubstitutionProof

module
public import LogicLineages.OrdinalComparison.SourceNamedSyntaxTargets
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedSyntaxProof
open SourceNamedSyntax SourceNamedSyntaxTargets SourceTypeSupport SourceFreeOccurrences

theorem namedResolution : NamedResolution := by
  intro Γ
  induction Γ with
  | nil => intro x σ h; cases h
  | cons a Γ ih =>
    rcases a with ⟨y, τ⟩
    intro x σ h
    by_cases e : x = y
    · subst x
      have ht : τ = σ := by simpa [lookup] using h
      subst σ
      simp only [resolve, dif_pos rfl]
      change y = y ∧ True
      exact ⟨rfl, trivial⟩
    · have hh : lookup Γ x = some σ := by simpa [lookup, e] using h
      have hi := ih x σ hh
      simp only [resolve, dif_neg e]
      change variableName (resolve Γ x hh) = x ∧
        (variableName (resolve Γ x hh) ≠ y ∧ Visible (resolve Γ x hh))
      exact ⟨hi.1, fun h => e (hi.1.symm.trans h), hi.2⟩

theorem namedSupportCalibration : NamedSupportCalibration := by
  intro Symbol arity Γ τ t
  induction t with
  | var => rfl
  | app f a ihf iha => simp [erase, typeSupport, namedSupport, ihf, iha]
  | lam x body ih =>
    change _ ∪ typeSupport (erase body) = _ ∪ namedSupport body
    exact congrArg (fun s => _ ∪ s) ih
  | zeroC => rfl
  | succC => rfl
  | caseC => rfl
  | recC => rfl
  | ranked s args ih => simp [erase, typeSupport, namedSupport, ih]

theorem namedDepthCalibration : NamedDepthCalibration := by
  intro Symbol arity Γ τ t
  induction t with
  | var => rfl
  | app f a ihf iha => simp [erase, lambdaDepth, namedDepth, ihf, iha]
  | lam x body ih =>
    change lambdaDepth (erase body) + 1 = namedDepth body + 1
    exact congrArg (fun n => n + 1) ih
  | zeroC => rfl
  | succC => rfl
  | caseC => rfl
  | recC => rfl
  | ranked s args ih => simp [erase, lambdaDepth, namedDepth, ih]

theorem namedOccurrenceTyping : NamedOccurrenceTyping := by
  intro Symbol arity Γ τ t
  induction t with
  | var x h => intro v hv; simpa [namedOccurrences] using (show v = (x, _) → _ from fun e => e ▸ h) (by simpa [namedOccurrences] using hv)
  | app f a ihf iha =>
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact ihf v h
    · exact iha v h
  | lam x body ih =>
    intro v hv
    have hm := List.mem_filter.mp hv
    have hx : v.1 ≠ x := by simpa using hm.2
    simpa [lookup, hx] using ih v hm.1
  | zeroC | succC | caseC | recC => simp [namedOccurrences]
  | ranked s args ih =>
    intro v hv
    rcases List.mem_flatten.mp hv with ⟨vs, hvs, hv⟩
    rcases List.mem_ofFn.mp hvs with ⟨i, rfl⟩
    exact ih i v hv

private theorem erased_visible {Symbol : Type} {arity : Symbol → Nat} {Γ : Context} {τ : Ty}
    (t : NamedTerm Symbol arity Γ τ) :
    ∀ v ∈ freeOccurrences (erase t), Visible (Γ := Γ) v.2 := by
  induction t with
  | var x h =>
    intro v hv
    have he : v = ⟨_, resolve _ x h⟩ := by simpa [erase, freeOccurrences] using hv
    subst v
    exact (namedResolution _ _ _ h).2
  | app f a ihf iha =>
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact ihf v h
    · exact iha v h
  | lam x body ih =>
    intro v hv
    rcases List.mem_filterMap.mp hv with ⟨w, hw, he⟩
    have hi := ih w hw
    rcases w with ⟨σ, w⟩
    cases w with
    | here => simp [dropBound] at he
    | there w =>
      have he' : (⟨_, w⟩ : PackedVariable _) = v := Option.some.inj he
      subst v
      exact hi.2
  | zeroC | succC | caseC | recC => simp [erase, freeOccurrences]
  | ranked s args ih =>
    intro v hv
    rcases List.mem_flatten.mp hv with ⟨vs, hvs, hv⟩
    rcases List.mem_ofFn.mp hvs with ⟨i, rfl⟩
    exact ih i v hv

private theorem filter_names {Γ : Context} {σ : Ty} (x : Nat)
    (vs : List (PackedVariable (contextTypes ((x, σ) :: Γ))))
    (hv : ∀ v ∈ vs, Visible (Γ := (x, σ) :: Γ) v.2) :
    (vs.filterMap dropBound).map (namePacked (Γ := Γ)) =
      (vs.map (namePacked (Γ := (x, σ) :: Γ))).filter (fun v => v.1 != x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem _ hw))
    have hh := hv v (by simp)
    rcases v with ⟨τ, v⟩
    cases v with
    | here =>
      change (vs.filterMap dropBound).map namePacked =
        ((x, σ) :: vs.map namePacked).filter (fun v => v.1 != x)
      simpa only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, if_false] using ht
    | there v =>
      change namePacked ⟨τ, v⟩ :: (vs.filterMap dropBound).map namePacked =
        ((variableName v, τ) :: vs.map namePacked).filter (fun v => v.1 != x)
      have hne : variableName (Γ := Γ) v ≠ x := hh.1
      simp only [List.filter_cons, bne_iff_ne]
      rw [if_pos hne]
      exact congrArg (List.cons (namePacked ⟨τ, v⟩)) ht

theorem namedOccurrenceCalibration : NamedOccurrenceCalibration := by
  intro Symbol arity Γ τ t
  induction t with
  | var x h => simp [erase, freeOccurrences, namedOccurrences, namePacked, (namedResolution _ _ _ h).1]
  | app f a ihf iha => simp [erase, freeOccurrences, namedOccurrences, ihf, iha]
  | lam x body ih =>
    change ((freeOccurrences (erase body)).filterMap dropBound).map namePacked =
      (namedOccurrences body).filter (fun v => v.1 != x)
    rw [filter_names x _ (erased_visible body), ih]
  | zeroC | succC | caseC | recC => rfl
  | ranked s args ih =>
    simp only [erase, freeOccurrences, namedOccurrences, List.map_flatten, List.map_ofFn]
    congr 2
    funext i
    exact ih i

end LogicLineages.OrdinalComparison.Source.SourceNamedSyntaxProof

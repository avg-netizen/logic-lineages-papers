import LogicLineages.PersistentMarking.DecisionSourceMarkProof
namespace LogicLineages.PersistentMarking.DecisionSourceOwnerProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof

theorem domainsIn (K : List Ty) (domains : List Ty) (τ : Ty) (hk : Closed K)
    (ht : ArrowPrefix domains τ ∈ K) : ∀ σ, σ ∈ domains → σ ∈ K := by
  induction domains with
  | nil => intro σ h; cases h
  | cons α rest ih =>
    have ha : α ∈ K := hk _ ht α (List.mem_cons_of_mem _ (List.mem_append_left _ (subtypeSelf α)))
    have hr : ArrowPrefix rest τ ∈ K := hk _ ht _ (List.mem_cons_of_mem _ (List.mem_append_right _ (subtypeSelf _)))
    intro σ h; rcases List.mem_cons.mp h with rfl|h
    · exact ha
    · exact ih hr σ h

theorem copies (K V H Γ f τ bs es domains) (hk : Closed K)
    (hu : Universe K V H Γ (.marked f τ bs es)) (hd : ∀ σ, σ ∈ domains → σ ∈ K) :
    ArgsUniverse K V H Γ (ownerCopies f bs es domains) := by
  induction domains with
  | nil => trivial
  | cons σ rest ih =>
    exact ⟨DecisionSourceMarkProof.sourceRetype K V H Γ f σ τ bs es hk hu (hd σ List.mem_cons_self),
      ih (fun υ hυ => hd υ (List.mem_cons_of_mem _ hυ))⟩

theorem ownerTuple : DecisionSourceTargets.SourceOwnerTuple := by
  intro K V H Γ f τ bs es domains q i hk hu hat hq
  have hqu : Universe K V H Γ q := hat.elim
    (fun h => sourceAt K V H Γ bs i q (markedBase _ _ _ _ _ _ _ _ hu) h)
    (fun h => sourceAt K V H Γ es i q (markedExtras _ _ _ _ _ _ _ _ hu) h)
  have hty : ArrowPrefix domains τ ∈ K := by
    simpa only [SpineShiftProof.annotationExact _ _ _ hq] using rootType K V H Γ q hqu
  exact copies K V H Γ f τ bs es domains hk hu (domainsIn K domains τ hk hty)
end LogicLineages.PersistentMarking.DecisionSourceOwnerProof

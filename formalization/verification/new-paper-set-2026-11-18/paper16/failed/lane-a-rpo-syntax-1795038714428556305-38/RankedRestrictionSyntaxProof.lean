import LogicLineages.PersistentMarking.RankedRestrictionTargets
import LogicLineages.PersistentMarking.DecisionOccurrenceProof
import LogicLineages.PersistentMarking.TypeSupportFoundationProof
import LogicLineages.PersistentMarking.PortHeadObservationProof
import LogicLineages.PersistentMarking.RefinementMarkProof

namespace LogicLineages.PersistentMarking.RankedRestrictionSyntaxProof
open Spine TypeSupport RankedRestrictionTargets

def ArgsTerm (S : Signature) (qs : Args) : Prop :=
  ∀ i q, At qs i q → Term S q

theorem annotation (q : Expr) (h : Ranked q) : q.type = .ground := by
  cases q with
  | free σ x => cases σ <;> first | rfl | cases h
  | bound | lam | marked => cases h
  | head f bs =>
    have hF := h.1
    cases f <;> first | rfl | cases hF

theorem termOrdinary (q : Expr) :
    Ranked q → Ordinary q ∧ (∀ τ, τ ∈ support q → τ = .ground) := by
  apply @Expr.rec (fun q => Ranked q → Ordinary q ∧ (∀ τ, τ ∈ support q → τ = .ground))
    (fun qs => RankedArgs qs → OrdinaryArgs qs ∧ (∀ τ, τ ∈ supportArgs qs → τ = .ground))
  · intro σ x h
    cases σ with
    | ground => simp [Ordinary,support,subtypes]
    | arrow => cases h
  · intro σ i h; cases h
  · intro σ q _ h; cases h
  · intro f bs ih h
    have hF := h.1
    obtain ⟨ho,hs⟩ := ih h.2
    cases f <;> try cases hF
    change OrdinaryArgs bs ∧ _
    refine ⟨ho,?_⟩
    intro τ hτ
    rcases List.mem_append.mp hτ with hτ | hτ
    · simpa [Head.result,subtypes] using hτ
    · exact hs τ hτ
  · intro f σ bs es _ _ h; cases h
  · simp [RankedArgs,OrdinaryArgs,supportArgs]
  · intro q qs ih ih' h
    obtain ⟨hq,hqt⟩ := ih h.1
    obtain ⟨hs,hst⟩ := ih' h.2
    exact ⟨⟨hq,hs⟩,fun τ hτ => (List.mem_append.mp hτ).elim (hqt τ) (hst τ)⟩

theorem included (s t : Expr) (hs : Ranked s) (ht : Ranked t) : TypeSupport.Included t s := by
  intro ρ hρ
  rw [(termOrdinary t ht).2 ρ hρ]
  exact TypeSupportFoundationProof.rootSupport s .ground (by rw [annotation s hs]; exact List.mem_cons_self)

theorem rankedAt {qs : Args} {i : Nat} {q : Expr} (h : At qs i q) (hs : RankedArgs qs) : Ranked q := by
  induction h with
  | here => exact hs.1
  | there _ ih => exact ih hs.2

theorem baseAt (S : Signature) (f : Head) (bs : Args) (h : Term S (.head f bs)) : ArgsTerm S bs := by
  intro i q ha
  have hr := rankedAt ha h.2.2
  have hOcc : DecisionObservations.Occurs [] (.head f bs) [] q :=
    .head (PortHeadObservationProof.atOccurrence [] bs i q ha)
  have ht := DecisionOccurrenceProof.typed [] (.head f bs) .ground [] q h.1.1 hOcc
  have hv := DecisionOccurrenceProof.valid S [] (.head f bs) [] q h.1.2 hOcc
  exact ⟨⟨annotation q hr ▸ ht,hv⟩,hr⟩

theorem remove (S : Signature) {ts rest : Args} {t : Expr} (h : Remove ts t rest)
    (ht : ArgsTerm S ts) : Term S t ∧ ArgsTerm S rest := by
  induction h with
  | here => exact ⟨ht _ _ .here,fun _ _ h => ht _ _ (.there h)⟩
  | there _ ih =>
    obtain ⟨hTerm,hTail⟩ := ih (fun _ _ h => ht _ _ (.there h))
    refine ⟨hTerm,?_⟩
    intro i q hq
    cases hq with
    | here => exact ht _ _ .here
    | there hq => exact hTail _ _ hq

theorem split (S : Signature) {xs ys zs : Args} (h : Split xs ys zs) (hx : ArgsTerm S xs) :
    ArgsTerm S ys ∧ ArgsTerm S zs := by
  induction h with
  | nil => exact ⟨fun _ _ h => nomatch h,fun _ _ h => nomatch h⟩
  | left _ ih =>
    obtain ⟨hl,hr⟩ := ih (fun _ _ h => hx _ _ (.there h))
    refine ⟨?_,hr⟩
    intro i q h
    cases h with
    | here => exact hx _ _ .here
    | there h => exact hl _ _ h
  | right _ ih =>
    obtain ⟨hl,hr⟩ := ih (fun _ _ h => hx _ _ (.there h))
    refine ⟨hl,?_⟩
    intro i q h
    cases h with
    | here => exact hx _ _ .here
    | there h => exact hr _ _ h

theorem markEq (S : Signature) (f : Head) (bs : Args) (h : Term S (.head f bs)) :
    mark (.head f bs) = some (.marked f .ground bs .nil) := by
  change some (.marked f f.result bs .nil) = _
  have he : f.result = .ground := annotation _ h.2
  rw [he]

theorem rootMarked (S : Signature) (f : Head) (bs : Args) (h : Term S (.head f bs)) :
    PaperTerm S (.marked f .ground bs .nil) .ground :=
  RefinementMarkProof.markPaper S (.head f bs) .ground _ h.1 (markEq S f bs h)

end LogicLineages.PersistentMarking.RankedRestrictionSyntaxProof

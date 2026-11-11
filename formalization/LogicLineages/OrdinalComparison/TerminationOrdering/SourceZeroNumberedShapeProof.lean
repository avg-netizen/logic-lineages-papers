module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedShapeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability

theorem actualZeroNumberedStep : SourceZeroNumberedComputabilityTargets.ActualZeroNumberedStep := by
  intro Symbol arity symbols S above Gamma f tau base types extras r
  constructor
  · intro h
    cases h with
    | numberedBase _ _ _ _ target _ _ hs => exact Or.inr (Or.inl ⟨target,hs,rfl⟩)
    | numberedExtras _ _ _ _ _ _ target hs => exact Or.inr (Or.inr ⟨target,hs,rfl⟩)
    | bottom q hn => exact Or.inl rfl
  · rintro (rfl | ⟨target,hs,rfl⟩ | ⟨target,hs,rfl⟩)
    · exact .bottom _ (by intro he; cases he)
    · exact .numberedBase 0 f tau base target types extras hs
    · exact .numberedExtras 0 f tau base types extras target hs

theorem primaryLabel {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    numberedLabel q = numberedLabel r := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h k ih ik => exact ih.trans ik
  all_goals first | rfl | trivial

theorem primaryTypedCode {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
    (hc : SubtypeClosed (fun t => t ∈ S)) {q r : Packed (Fin n) arity Gamma}
    (hq : InUniverse symbols S q.2) (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    (q.1,representativeCode symbols S q) = (r.1,representativeCode symbols S r) := by
  have hr := (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma q r h).mp hq
  have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma q r
    (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma q r h)
  exact Prod.ext ht ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q r hq hr).mpr h)

theorem argumentCodesPrimary {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma types : List Ty}
    (hc : SubtypeClosed (fun t => t ∈ S)) {a b : AuxArguments (Fin n) arity Gamma types}
    (h : WindowArgumentPrimary (Fin n) arity symbols S Gamma types a b)
    (ha : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ S) (HeadInWindow arity symbols S) a) :
    argumentCodes symbols S a = argumentCodes symbols S b := by
  induction types with
  | nil => cases h; rfl
  | cons sigma types ih => cases h with
    | cons q r rest target hq ht =>
      have he := primaryTypedCode hc (q := ⟨sigma,q⟩) (r := ⟨sigma,r⟩) ⟨ha.1.1,ha.2.1⟩ hq
      have het := ih ht ⟨ha.1.2,ha.2.2⟩
      simpa only [argumentCodes,argumentList,List.map_cons] using congrArg₂ List.cons he het

theorem primaryMembers {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S : List Ty}
    (hc : SubtypeClosed (fun t => t ∈ S)) {Gamma : List Ty} {q r : Packed (Fin n) arity Gamma}
    (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    InUniverse symbols S q.2 → (numberedMembers symbols S q).Perm (numberedMembers symbols S r) := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl q => intro _; exact List.Perm.refl _
  case symm h ih =>
    intro hq
    exact (ih ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mpr hq)).symm
  case trans h k ih ik =>
    intro hq
    exact (ih hq).trans (ik ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mp hq))
  case numbered k f g tau base target types extras hf hg he hp =>
    intro _
    exact (hp.map (fun p => (p.1,representativeCode symbols S p))).append_right _
  case numberedBase k f tau base target types extras h ih =>
    intro hq
    have he := argumentCodesPrimary hc h ⟨hq.1.2.1,hq.2.2.1⟩
    simp only [numberedMembers,he]
    exact List.Perm.refl _
  case numberedExtras k f tau base types extras target h ih =>
    intro hq
    have he := argumentCodesPrimary hc h ⟨hq.1.2.2,hq.2.2.2⟩
    simp only [numberedMembers,he]
    exact List.Perm.refl _
  all_goals first | (intro _; exact List.Perm.refl _) | trivial

theorem actualPrimaryNumberedMembers : SourceZeroNumberedComputabilityTargets.ActualPrimaryNumberedMembers := by
  intro n arity symbols S hc Gamma q r hq h
  exact ⟨primaryLabel h,primaryMembers hc h hq⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedShapeProof

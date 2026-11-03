module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedWindowEquivalence NumberedWindowTraces NumberedLeastCodeRepresentative NumberedQuotientPaths

theorem edgeCalibration : NumberedQuotientPathsTargets.ActualEdgeCalibration := by
  intro n arity symbols S hc above Gamma q r hq hr
  constructor
  · rintro ⟨tau,a,b,ha,hs,hea,heb⟩
    have hb := NumberedWindowReductionProof.stepGood symbols S hc hs ha
    exact ⟨tau,a,b,
      (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q ⟨tau,a⟩ hq ha).mp hea.symm,
      hs,(NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma ⟨tau,b⟩ r hb hr).mp heb⟩
  · rintro ⟨tau,a,b,hqa,hs,hbr⟩
    have ha := (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma q ⟨tau,a⟩ hqa).mp hq
    have hb := NumberedWindowReductionProof.stepGood symbols S hc hs ha
    exact ⟨tau,a,b,ha,hs,
      ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q ⟨tau,a⟩ hq ha).mpr hqa).symm,
      (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma ⟨tau,b⟩ r hb hr).mpr hbr⟩

theorem countedForward : NumberedQuotientPathsTargets.ActualCountedForward := by
  intro n arity symbols S hc above Gamma count q r hq h
  revert hq
  induction h with
  | equivalent he =>
    intro hq
    have hr := (NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S Gamma _ _ he).mp hq
    have hcoded := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma _ _ hq hr).mpr he
    rw [hcoded]
    exact .refl _
  | raw q r hs => intro hq; exact .step ⟨_,q,r,hq,hs,rfl,rfl⟩
  | trans h1 h2 ih1 ih2 =>
    intro hq
    exact .trans (ih1 hq) (ih2 (NumberedWindowTracesProof.endpoint hc h1 hq))

theorem liftPath {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    (hc : SubtypeClosed (fun tau => tau∈S)) (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    {count x y : Nat} (h : CountedPath (QuotientEdge n arity symbols S above Gamma) count x y) :
    ∀ q : Packed (Fin n) arity Gamma,InUniverse symbols S q.2 → representativeCode symbols S q=x →
      ∃ r : Packed (Fin n) arity Gamma,InUniverse symbols S r.2 ∧ representativeCode symbols S r=y ∧
        WindowTrace (Fin n) arity symbols S above Gamma count q r := by
  induction h with
  | refl x => intro q hq he; exact ⟨q,hq,he,.equivalent (.refl q)⟩
  | step he =>
    intro q hq hcode
    obtain ⟨tau,a,b,ha,hs,hax,hby⟩ := he
    have hb := NumberedWindowReductionProof.stepGood symbols S hc hs ha
    have hqa := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q ⟨tau,a⟩ hq ha).mp (hcode.trans hax.symm)
    exact ⟨⟨tau,b⟩,hb,hby,.trans (.equivalent hqa) (.raw a b hs)⟩
  | trans h1 h2 ih1 ih2 =>
    intro q hq hcode
    obtain ⟨r,hr,her,hqr⟩ := ih1 q hq hcode
    obtain ⟨s,hs,hes,hrs⟩ := ih2 r hr her
    exact ⟨s,hs,hes,.trans hqr hrs⟩

theorem countedBackward : NumberedQuotientPathsTargets.ActualCountedBackward := by
  intro n arity symbols S hc above Gamma count q r hq hr h
  obtain ⟨t,ht,het,hqt⟩ := liftPath symbols S hc above Gamma h q hq rfl
  have htr := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma t r ht hr).mp het
  simpa only [Nat.add_zero] using WindowTrace.trans hqt (WindowTrace.equivalent htr)

theorem pathDichotomy {H : Nat → Nat → Prop} {count x y : Nat} (h : CountedPath H count x y) :
    (count=0 ∧ x=y) ∨ PositivePath H x y := by
  induction h with
  | refl => exact Or.inl ⟨rfl,rfl⟩
  | step h => exact Or.inr (.step h)
  | trans h1 h2 ih1 ih2 =>
    rcases ih1 with ⟨hm,he⟩ | hp
    · rcases ih2 with ⟨hn,he'⟩ | hp'
      · exact Or.inl ⟨by omega,he.trans he'⟩
      · exact Or.inr (he.symm ▸ hp')
    · rcases ih2 with ⟨hn,he⟩ | hp'
      · exact Or.inr (he ▸ hp)
      · exact Or.inr (.trans hp hp')

theorem positiveClosure : NumberedQuotientPathsTargets.ActualPositiveClosure := by
  intro n arity symbols S above Gamma x y
  constructor
  · intro h
    induction h with
    | step h => exact ⟨1,by omega,.step h⟩
    | trans h1 h2 ih1 ih2 =>
      obtain ⟨m,hm,hp⟩ := ih1
      obtain ⟨k,hk,hq⟩ := ih2
      exact ⟨m+k,by omega,.trans hp hq⟩
  · rintro ⟨count,hpos,h⟩
    rcases pathDichotomy h with ⟨hz,_⟩ | hp
    · omega
    · exact hp

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsProof

module
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearchTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearch

private theorem computableOr {α : Type*} [Primcodable α] {f g : α → Bool}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => f x || g x) := by
  exact (hf.cond (Computable.const true) hg).of_eq (fun x => by cases f x <;> rfl)

theorem prefixCorrect : Targets.PrefixCorrect := by
  intro bad q n
  induction n with
  | zero => simp [prefixBad]
  | succ n ih =>
    simp only [prefixBad, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨r, hr, hb⟩ | hb)
      · exact ⟨r, Nat.le_succ_of_le hr, hb⟩
      · exact ⟨n + 1, le_rfl, hb⟩
    · rintro ⟨r, hr, hb⟩
      rcases Nat.lt_or_eq_of_le hr with hr | rfl
      · exact Or.inl ⟨r, Nat.le_of_lt_succ hr, hb⟩
      · exact Or.inr hb

theorem prefixComputable : Targets.PrefixComputable := by
  intro bad hb
  have hs : Computable₂ (fun (p : Nat × Nat) (s : Nat × Bool) =>
      s.2 || bad p.1 (s.1 + 1)) :=
    computableOr (Computable.snd.comp Computable.snd)
      (hb.comp (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
  have hc := Computable.nat_rec (σ := Bool) (α := Nat × Nat)
    Computable.snd (hb.comp Computable.fst (Computable.const 0)) hs
  apply hc.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [prefixBad, ih]

private theorem notGood (bad : Nat → Nat → Bool) (q : Nat) :
    ¬ Good bad q ↔ ∃ r, bad q r = true := by
  classical
  simp only [Good, not_forall, Bool.not_eq_false]

theorem complementEnumerable : Targets.ComplementEnumerable := by
  intro bad hb
  apply (Partrec.rfind hb.partrec₂).dom_re.of_eq
  intro q
  rw [notGood]
  simp [Nat.rfind_dom]

theorem decisionIffBound : Targets.DecisionIffBound := by
  intro bad hb
  constructor
  · intro hgood
    obtain ⟨d, hd, heq⟩ := ComputablePred.computable_iff.mp hgood
    have hdgood : ∀ q, d q = true ↔ Good bad q := by
      intro q
      rw [heq]
    let P : Nat → Nat → Prop := fun q r => (d q || bad q r) = true
    have hp : ComputablePred (fun p : Nat × Nat => P p.1 p.2) := by
      apply Computable.computablePred
      simpa [P] using computableOr (hd.comp Computable.fst) hb
    have hex : ∀ q, ∃ r, P q r := by
      intro q
      by_cases h : Good bad q
      · exact ⟨0, by simp [P, (hdgood q).mpr h]⟩
      · obtain ⟨r, hr⟩ := (notGood bad q).mp h
        exact ⟨r, by simp [P, hr]⟩
    refine ⟨fun q => Nat.find (hex q), Computable.find hp hex, ?_⟩
    intro q hq
    refine ⟨Nat.find (hex q), le_rfl, ?_⟩
    have h := Nat.find_spec (hex q)
    have hor : d q = true ∨ bad q (Nat.find (hex q)) = true := by
      simpa only [P, Bool.or_eq_true] using h
    rcases hor with h | h
    · exact False.elim (hq ((hdgood q).mp h))
    · exact h
  · rintro ⟨b, hbcomp, hbound⟩
    have hp := (prefixComputable bad hb).comp Computable.id hbcomp
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun q => !(prefixBad bad q (b q)), Primrec.not.to_comp.comp hp, ?_⟩
    funext q
    apply propext
    change Good bad q ↔ (!(prefixBad bad q (b q))) = true
    have hnot : (!(prefixBad bad q (b q))) = true ↔ prefixBad bad q (b q) = false := by
      cases prefixBad bad q (b q) <;> decide
    rw [hnot]
    constructor
    · intro hq
      cases h : prefixBad bad q (b q) with
      | false => rfl
      | true =>
        obtain ⟨r, _, hr⟩ := (prefixCorrect bad q (b q)).mp h
        simp [hq r] at hr
    · intro hprefix
      by_contra hq
      obtain ⟨r, hr, hbad⟩ := hbound q hq
      have htrue := (prefixCorrect bad q (b q)).mpr ⟨r, hr, hbad⟩
      simp [hprefix] at htrue
end LogicLineages.ComputabilityKnowledge.SourceCounterBoundSearch

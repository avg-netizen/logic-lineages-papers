module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearNameProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearProof
open BlockRows TiedLinear

private theorem moved_parameter_step (r : Row) (t : Term) (c : Int) (j : Nat) :
    j ∈ Row.parameters ((.add (.multiply c.toNat t) r.1.1,
      .add (.multiply (-c).toNat t) r.1.2), r.2) ↔
        j ∈ t.variables ∨ j ∈ r.parameters := by
  simp only [Row.parameters, Term.variables, List.mem_append]
  tauto

private theorem lower_entries_parameters (table : List Token) (x : Nat) (positive negative : Term)
    (entries : List (Int × NormalForm.Summand)) (j : Nat)
    (hj : j ∈ (lowerEntries table x positive negative entries).parameters) :
    j ∈ positive.variables ∨ j ∈ negative.variables ∨
      ∃ a ∈ entries, ∃ t, lowerSummand table x a.2 = .parameter t ∧ j ∈ t.variables := by
  induction entries with
  | nil => exact (List.mem_append.mp hj).elim Or.inl (fun h => Or.inr (Or.inl h))
  | cons a entries ih =>
    have liftTail : (j ∈ positive.variables ∨ j ∈ negative.variables ∨
        ∃ b ∈ entries, ∃ t, lowerSummand table x b.2 = .parameter t ∧ j ∈ t.variables) →
        j ∈ positive.variables ∨ j ∈ negative.variables ∨
        ∃ b ∈ a :: entries, ∃ t, lowerSummand table x b.2 = .parameter t ∧ j ∈ t.variables := by
      rintro (hP | hN | ⟨b, hb, t, he, ht⟩)
      · exact Or.inl hP
      · exact Or.inr (Or.inl hN)
      · exact Or.inr (Or.inr ⟨b, List.mem_cons_of_mem _ hb, t, he, ht⟩)
    cases ht : lowerSummand table x a.2 with
    | parameter t =>
      have he : j ∈ (lowerEntries table x positive negative (a :: entries)).parameters ↔
          j ∈ t.variables ∨ j ∈ (lowerEntries table x positive negative entries).parameters := by
        simp only [lowerEntries, ht]
        exact moved_parameter_step (lowerEntries table x positive negative entries) t a.1 j
      rcases he.mp hj with h | h
      · exact Or.inr (Or.inr ⟨a, List.mem_cons_self, t, ht, h⟩)
      · exact liftTail (ih h)
    | occurrence s =>
      apply liftTail
      apply ih
      simpa only [lowerEntries, ht, Row.parameters] using hj

private theorem lower_row_parameters (table : List Token) (x : Nat) (r : NormalForm.Row)
    (hp : PureRow r) (j : Nat) (hj : j ∈ (lowerRow table x r).parameters) :
    ∃ code ∈ NormalForm.rowVariables r, ∃ t,
      tokenOfName table x code = .parameter t ∧ j ∈ t.variables := by
  have h := lower_entries_parameters table x (.numeral r.1.toNat)
    (.numeral (-r.1).toNat) r.2 j hj
  simp only [Term.variables, List.not_mem_nil, false_or] at h
  obtain ⟨a, ha, t, he, hjt⟩ := h
  obtain ⟨code, hvar⟩ := hp a ha
  refine ⟨code, List.mem_map.mpr ⟨a, ha, ?_⟩, t, ?_, hjt⟩
  · rw [hvar]; rfl
  · simpa only [hvar, lowerSummand] using he

private theorem lower_formula_parameters (table : List Token) (x : Nat) (p : NormalForm.Formula)
    (hp : PureFormula p) (j : Nat) (hj : j ∈ (lowerFormula table x p).parameters) :
    ∃ code ∈ p.variables, ∃ t, tokenOfName table x code = .parameter t ∧ j ∈ t.variables := by
  induction p with
  | truth => simp [lowerFormula, Formula.parameters] at hj
  | falsity => simp [lowerFormula, Formula.parameters] at hj
  | atom a => cases a <;> exact lower_row_parameters table x _ hp j hj
  | negative p ih => exact ih hp hj
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · obtain ⟨code, hc, t, he, ht⟩ := ihp hp.1 h
      exact ⟨code, List.mem_append_left _ hc, t, he, ht⟩
    · obtain ⟨code, hc, t, he, ht⟩ := ihq hp.2 h
      exact ⟨code, List.mem_append_right _ hc, t, he, ht⟩
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · obtain ⟨code, hc, t, he, ht⟩ := ihp hp.1 h
      exact ⟨code, List.mem_append_left _ hc, t, he, ht⟩
    · obtain ⟨code, hc, t, he, ht⟩ := ihq hp.2 h
      exact ⟨code, List.mem_append_right _ hc, t, he, ht⟩

theorem wholeBlockParameterIndependence : TiedLinearTargets.WholeBlockParameterIndependence := by
  intro bound x p hparams j hj hnew
  obtain ⟨code, hc, t, hdecode, hjt⟩ := lower_formula_parameters (tokens p) x _
    (pure_eliminated (tokens p) x p) j hnew
  obtain ⟨u, hu, he, _⟩ := surviving_token x p code hc
  have hut : u = .parameter t := he.symm.trans hdecode
  rw [hut] at hu
  exact hparams j hj (parameter_token_support p t hu j hjt)

private theorem lower_entries_occurrences (table : List Token) (x : Nat) (positive negative : Term)
    (entries : List (Int × NormalForm.Summand)) (s : NormalForm.Summand)
    (hs : s ∈ (lowerEntries table x positive negative entries).2.map Prod.snd) :
    ∃ a ∈ entries, lowerSummand table x a.2 = .occurrence s := by
  induction entries with
  | nil => simp [lowerEntries] at hs
  | cons a entries ih =>
    cases ht : lowerSummand table x a.2 with
    | parameter t =>
      have htail : s ∈ (lowerEntries table x positive negative entries).2.map Prod.snd := by
        simpa only [lowerEntries, ht] using hs
      obtain ⟨b, hb, he⟩ := ih htail
      exact ⟨b, List.mem_cons_of_mem _ hb, he⟩
    | occurrence t =>
      have hcons : s ∈ t :: (lowerEntries table x positive negative entries).2.map Prod.snd := by
        simpa only [lowerEntries, ht, List.map_cons] using hs
      rcases List.mem_cons.mp hcons with h | h
      · subst s
        exact ⟨a, List.mem_cons_self, ht⟩
      · obtain ⟨b, hb, he⟩ := ih h
        exact ⟨b, List.mem_cons_of_mem _ hb, he⟩

private theorem lower_row_occurrences (table : List Token) (x : Nat) (r : NormalForm.Row)
    (hp : PureRow r) (s : NormalForm.Summand)
    (hs : s ∈ (lowerRow table x r).2.map Prod.snd) :
    ∃ code ∈ NormalForm.rowVariables r, tokenOfName table x code = .occurrence s := by
  obtain ⟨a, ha, he⟩ := lower_entries_occurrences table x (.numeral r.1.toNat)
    (.numeral (-r.1).toNat) r.2 s hs
  obtain ⟨code, hvar⟩ := hp a ha
  refine ⟨code, List.mem_map.mpr ⟨a, ha, ?_⟩, ?_⟩
  · rw [hvar]; rfl
  · simpa only [hvar, lowerSummand] using he

private theorem lower_formula_occurrences (table : List Token) (x : Nat) (p : NormalForm.Formula)
    (hp : PureFormula p) (s : NormalForm.Summand)
    (hs : s ∈ (PlainMaximum.occurrences (lowerFormula table x p)).map Prod.snd) :
    ∃ code ∈ p.variables, tokenOfName table x code = .occurrence s := by
  induction p with
  | truth => simp [lowerFormula, PlainMaximum.occurrences] at hs
  | falsity => simp [lowerFormula, PlainMaximum.occurrences] at hs
  | atom a => cases a <;> exact lower_row_occurrences table x _ hp s hs
  | negative p ih => exact ih hp hs
  | conjunction p q ihp ihq =>
    have hmem : s ∈ (PlainMaximum.occurrences (lowerFormula table x p)).map Prod.snd ++
        (PlainMaximum.occurrences (lowerFormula table x q)).map Prod.snd := by
      simpa only [lowerFormula, PlainMaximum.occurrences, List.map_append] using hs
    rcases List.mem_append.mp hmem with h | h
    · obtain ⟨code, hc, he⟩ := ihp hp.1 h
      exact ⟨code, List.mem_append_left _ hc, he⟩
    · obtain ⟨code, hc, he⟩ := ihq hp.2 h
      exact ⟨code, List.mem_append_right _ hc, he⟩
  | disjunction p q ihp ihq =>
    have hmem : s ∈ (PlainMaximum.occurrences (lowerFormula table x p)).map Prod.snd ++
        (PlainMaximum.occurrences (lowerFormula table x q)).map Prod.snd := by
      simpa only [lowerFormula, PlainMaximum.occurrences, List.map_append] using hs
    rcases List.mem_append.mp hmem with h | h
    · obtain ⟨code, hc, he⟩ := ihp hp.1 h
      exact ⟨code, List.mem_append_left _ hc, he⟩
    · obtain ⟨code, hc, he⟩ := ihq hp.2 h
      exact ⟨code, List.mem_append_right _ hc, he⟩

theorem allowed_formula_iff (bound : List Nat) (p : Formula) :
    TiedLinear.allowed bound p = true ↔
      ∀ a ∈ PlainMaximum.occurrences p, PlainMaximum.allowedSummand bound a.2 = true := by
  induction p with
  | truth => simp [TiedLinear.allowed, PlainMaximum.occurrences]
  | falsity => simp [TiedLinear.allowed, PlainMaximum.occurrences]
  | atom a => simp only [TiedLinear.allowed, PlainMaximum.allowed,
      PlainMaximum.occurrences, List.all_eq_true]
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [TiedLinear.allowed, Bool.and_eq_true, ihp, ihq,
      PlainMaximum.occurrences, List.mem_append, or_imp, forall_and]
  | disjunction p q ihp ihq =>
    simp only [TiedLinear.allowed, Bool.and_eq_true, ihp, ihq,
      PlainMaximum.occurrences, List.mem_append, or_imp, forall_and]

private theorem allowed_erase (bound : List Nat) (x : Nat) (s : NormalForm.Summand)
    (hs : PlainMaximum.allowedSummand bound s = true) (hne : s.name ≠ x) :
    PlainMaximum.allowedSummand (bound.erase x) s = true := by
  cases s with
  | «variable» j =>
    have hj : j ∈ bound := by simpa [PlainMaximum.allowedSummand] using hs
    have hjx : j ≠ x := hne
    simpa [PlainMaximum.allowedSummand] using (List.mem_erase_of_ne hjx).mpr hj
  | phi j shift =>
    have hj : j ∈ bound ∧ shift = 0 := by simpa [PlainMaximum.allowedSummand] using hs
    have hjx : j ≠ x := hne
    simpa [PlainMaximum.allowedSummand] using
      And.intro ((List.mem_erase_of_ne hjx).mpr hj.1) hj.2
  | hyperPhi j e h => simp [PlainMaximum.allowedSummand] at hs

theorem remainingPlainClass : TiedLinearTargets.RemainingPlainClass := by
  intro bound x p hallowed hlinear
  apply (allowed_formula_iff (bound.erase x) (eliminate x p)).mpr
  intro a ha
  have hs : a.2 ∈ (PlainMaximum.occurrences (eliminate x p)).map Prod.snd :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨code, hc, hdecode⟩ := lower_formula_occurrences (tokens p) x _
    (pure_eliminated (tokens p) x p) a.2 hs
  obtain ⟨u, hu, he, hraw⟩ := surviving_token x p code hc
  have hut : u = .occurrence a.2 := he.symm.trans hdecode
  rw [hut] at hu hraw
  obtain ⟨b, hb, heq⟩ := List.mem_map.mp ((occurrence_token_mem p a.2).mp hu)
  have hsource : PlainMaximum.allowedSummand bound a.2 = true := by
    rw [← heq]
    exact (allowed_formula_iff bound p).mp hallowed b hb
  have hname : a.2.name ≠ x := by
    intro h
    have hx := linear_token_safe x p hlinear (.occurrence a.2) hu hraw
    exact hx (List.mem_singleton.mpr h.symm)
  exact allowed_erase bound x a.2 hsource hname

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearProof

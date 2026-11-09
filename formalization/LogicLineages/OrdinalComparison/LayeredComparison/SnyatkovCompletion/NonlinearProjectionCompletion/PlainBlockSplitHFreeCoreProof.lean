module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem hfree_add (a b : Term) (ha : termHFree a = true) (hb : termHFree b = true) :
    termHFree (.add a b) = true := by simp only [termHFree, ha, hb, Bool.true_and]
theorem hfree_subtract (a b : Term) (ha : termHFree a = true) (hb : termHFree b = true) :
    termHFree (.subtract a b) = true := by simp only [termHFree, ha, hb, Bool.true_and]

theorem hfree_term_substitution (t : Term) (i : Nat) (replacement : Term)
    (ht : termHFree t = true) (hr : termHFree replacement = true) :
    termHFree (t.substitute i replacement) = true := by
  induction t with
  | numeral n => rfl
  | «variable» j => by_cases he : j = i <;> simp [Term.substitute, he, termHFree, hr]
  | add a b iha ihb =>
    have h := Bool.and_eq_true_iff.mp ht
    exact hfree_add _ _ (iha h.1) (ihb h.2)
  | subtract a b iha ihb =>
    have h := Bool.and_eq_true_iff.mp ht
    exact hfree_subtract _ _ (iha h.1) (ihb h.2)
  | multiply c a ih => exact ih ht
  | divide c a ih => exact ih ht
  | phi a ih => exact ih ht
  | phiInverse a ih => exact ih ht
  | hyper a ih => simp [termHFree] at ht
  | hyperInverse a ih => simp [termHFree] at ht

theorem hfree_summand_term (s : NormalForm.Summand) (hs : summandHFree s = true) :
    termHFree s.term = true := by
  cases s with
  | «variable» i => rfl
  | phi i e => rfl
  | hyperPhi i e h => simp [summandHFree] at hs

theorem hfree_row_parts (r : Row) (hr : rowHFree r = true) :
    termHFree r.1.1 = true ∧ termHFree r.1.2 = true ∧
      ∀ a ∈ r.2, summandHFree a.2 = true := by
  obtain ⟨hpn, he⟩ := Bool.and_eq_true_iff.mp hr
  obtain ⟨hp, hn⟩ := Bool.and_eq_true_iff.mp hpn
  exact ⟨hp, hn, List.all_eq_true.mp he⟩

theorem hfree_row_of_parts (r : Row) (hp : termHFree r.1.1 = true)
    (hn : termHFree r.1.2 = true) (he : ∀ a ∈ r.2, summandHFree a.2 = true) :
    rowHFree r = true := by
  have hall : r.2.all (fun a => summandHFree a.2) = true := List.all_eq_true.mpr he
  simp only [rowHFree, hp, hn, hall, Bool.true_and]

def TokenHFree : TiedLinear.Token → Prop
  | .parameter t => termHFree t = true
  | .occurrence s => summandHFree s = true

theorem hfree_original_tokens (p : Formula) (hp : formulaHFree p = true) :
    ∀ t ∈ TiedLinear.tokens p, TokenHFree t := by
  induction p with
  | truth => intro t ht; exact False.elim (List.not_mem_nil ht)
  | falsity => intro t ht; exact False.elim (List.not_mem_nil ht)
  | atom a =>
    intro t ht
    have hr := hfree_row_parts a.row hp
    rcases List.mem_append.mp ht with hc | ho
    · rcases List.mem_cons.mp hc with he | hc
      · subst t; exact hr.1
      · have he : t = .parameter a.row.1.2 := List.mem_singleton.mp hc
        subst t; exact hr.2.1
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ho
      exact hr.2.2 b hb
  | negative p ih => exact ih hp
  | conjunction p q ihp ihq =>
    intro t ht
    have h := Bool.and_eq_true_iff.mp hp
    rcases List.mem_append.mp ht with ht | ht
    · exact ihp h.1 t ht
    · exact ihq h.2 t ht
  | disjunction p q ihp ihq =>
    intro t ht
    have h := Bool.and_eq_true_iff.mp hp
    rcases List.mem_append.mp ht with ht | ht
    · exact ihp h.1 t ht
    · exact ihq h.2 t ht

theorem hfree_lower_entries (table : List TiedLinear.Token) (x : Nat) (positive negative : Term)
    (entries : List (Int × NormalForm.Summand))
    (hp : termHFree positive = true) (hn : termHFree negative = true)
    (he : ∀ a ∈ entries, TokenHFree (TiedLinear.lowerSummand table x a.2)) :
    rowHFree (TiedLinear.lowerEntries table x positive negative entries) = true := by
  induction entries with
  | nil => exact hfree_row_of_parts _ hp hn (by simp [TiedLinear.lowerEntries])
  | cons a entries ih =>
    have htail := ih (fun b hb => he b (List.mem_cons_of_mem a hb))
    have hparts := hfree_row_parts _ htail
    have hhead := he a List.mem_cons_self
    cases ht : TiedLinear.lowerSummand table x a.2 with
    | parameter t =>
      rw [ht] at hhead
      simp only [TiedLinear.lowerEntries, ht]
      apply hfree_row_of_parts
      · exact hfree_add _ _ hhead hparts.1
      · exact hfree_add _ _ hhead hparts.2.1
      · exact hparts.2.2
    | occurrence s =>
      rw [ht] at hhead
      simp only [TiedLinear.lowerEntries, ht]
      apply hfree_row_of_parts
      · exact hparts.1
      · exact hparts.2.1
      · intro b hb
        rcases List.mem_cons.mp hb with h | h
        · subst b; exact hhead
        · exact hparts.2.2 b h

theorem hfree_lower_row (table : List TiedLinear.Token) (x : Nat) (r : NormalForm.Row)
    (hp : TiedLinearProof.PureRow r)
    (hh : ∀ code ∈ NormalForm.rowVariables r, TokenHFree (TiedLinear.tokenOfName table x code)) :
    rowHFree (TiedLinear.lowerRow table x r) = true := by
  apply hfree_lower_entries table x (.numeral r.1.toNat) (.numeral (-r.1).toNat) r.2 rfl rfl
  intro a ha
  obtain ⟨code, he⟩ := hp a ha
  have hc : code ∈ NormalForm.rowVariables r := List.mem_map.mpr ⟨a, ha, by rw [he]; rfl⟩
  simpa only [he, TiedLinear.lowerSummand] using hh code hc

theorem hfree_lower_formula (table : List TiedLinear.Token) (x : Nat) (p : NormalForm.Formula)
    (hp : TiedLinearProof.PureFormula p)
    (hh : ∀ code ∈ p.variables, TokenHFree (TiedLinear.tokenOfName table x code)) :
    formulaHFree (TiedLinear.lowerFormula table x p) = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> exact hfree_lower_row table x _ hp hh
  | negative p ih => exact ih hp hh
  | conjunction p q ihp ihq =>
    have hP := ihp hp.1 (fun code hc => hh code (List.mem_append_left _ hc))
    have hQ := ihq hp.2 (fun code hc => hh code (List.mem_append_right _ hc))
    exact (Bool.and_eq_true_iff (x := formulaHFree (TiedLinear.lowerFormula table x p))
      (y := formulaHFree (TiedLinear.lowerFormula table x q))).mpr ⟨hP, hQ⟩
  | disjunction p q ihp ihq =>
    have hP := ihp hp.1 (fun code hc => hh code (List.mem_append_left _ hc))
    have hQ := ihq hp.2 (fun code hc => hh code (List.mem_append_right _ hc))
    exact (Bool.and_eq_true_iff (x := formulaHFree (TiedLinear.lowerFormula table x p))
      (y := formulaHFree (TiedLinear.lowerFormula table x q))).mpr ⟨hP, hQ⟩

/-- The actual natural Cooper adapter only decodes surviving original tokens;
it introduces no H operation in arbitrary expanded parameter terms. -/
theorem hfree_tied_eliminate (x : Nat) (p : Formula) (hp : formulaHFree p = true) :
    formulaHFree (TiedLinear.eliminate x p) = true := by
  apply hfree_lower_formula (TiedLinear.tokens p) x _ (TiedLinearProof.pure_eliminated _ x p)
  intro code hc
  obtain ⟨t, ht, he, _⟩ := TiedLinearProof.surviving_token x p code hc
  rw [he]
  exact hfree_original_tokens p hp t ht

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof

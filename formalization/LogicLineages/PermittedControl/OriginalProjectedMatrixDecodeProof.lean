module
public import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalProjectedMatrixDecode
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand)
open HeterogeneousSignedMatrixSlice (Row)

private theorem exactTerm (ops : List LowerOperand) (t : Summand) (o : WeightedOperand) :
    decodeTerm ops t = some o ↔ LiteralTerm ops t o := by
  constructor
  · intro hit
    rcases t with ⟨w,s⟩
    cases s with
    | phi i shift => cases hit
    | hyperPhi i shift outer => cases hit
    | «variable» i =>
        cases i with
        | zero => cases hit
        | succ j =>
            by_cases h : j < ops.length
            · have eq : (w,ops[j]) = o := by
                simpa only [decodeTerm,List.getElem?_eq_getElem h,Option.map_some,Option.some.injEq] using hit
              exact ⟨j,h,rfl,eq.symm⟩
            · simp [decodeTerm,List.getElem?_eq_none (Nat.le_of_not_gt h)] at hit
  · rintro ⟨j,hj,variableAt,rfl⟩
    simp only [decodeTerm,variableAt,List.getElem?_eq_getElem hj,Option.map_some]

private theorem exactTerms (ops : List LowerOperand) (source : List Summand) (out : List WeightedOperand) :
    decodeTerms ops source = some out ↔ List.Forall₂ (LiteralTerm ops) source out := by
  induction source generalizing out with
  | nil =>
      constructor
      · intro h
        have eq : ([] : List WeightedOperand) = out := Option.some.inj h
        subst out
        exact .nil
      · intro h
        cases h
        rfl
  | cons s source ih =>
      constructor
      · intro h
        cases head : decodeTerm ops s with
        | none => simp [decodeTerms,head] at h
        | some t =>
            cases tail : decodeTerms ops source with
            | none => simp [decodeTerms,head,tail] at h
            | some rest =>
                have eq : t :: rest = out := by simpa [decodeTerms,head,tail] using h
                subst out
                exact .cons ((exactTerm ops s t).mp head) ((ih rest).mp tail)
      · intro h
        cases h with
        | cons one more =>
            simp [decodeTerms,(exactTerm ops _ _).mpr one,(ih _).mpr more]

private theorem exactRow (ops : List LowerOperand) (a : NormalForm.Atom) (r : Row) :
    decodeAtom ops a = some r ↔ LiteralRow ops a r := by
  constructor
  · intro hit
    cases h : decodeTerms ops a.row.2 with
    | none => simp [decodeAtom,h] at hit
    | some terms =>
        have eq : (testOf a,a.row.1,terms) = r := by simpa [decodeAtom,h] using hit
        subst r
        exact ⟨rfl,rfl,(exactTerms ops _ _).mp h⟩
  · rintro ⟨test,constant,terms⟩
    have h := (exactTerms ops _ _).mpr terms
    rcases r with ⟨test0,c,ts⟩
    simp only [decodeAtom,h,Option.map_some]
    exact congrArg some (Prod.ext test.symm (Prod.ext constant.symm rfl))

private theorem exactAtoms (ops : List LowerOperand) (source : List NormalForm.Atom) (out : List Row) :
    decodeAtoms ops source = some out ↔ List.Forall₂ (LiteralRow ops) source out := by
  induction source generalizing out with
  | nil =>
      constructor
      · intro h
        have eq : ([] : List Row) = out := Option.some.inj h
        subst out
        exact .nil
      · intro h
        cases h
        rfl
  | cons a source ih =>
      constructor
      · intro h
        cases head : decodeAtom ops a with
        | none => simp [decodeAtoms,head] at h
        | some t =>
            cases tail : decodeAtoms ops source with
            | none => simp [decodeAtoms,head,tail] at h
            | some rest =>
                have eq : t :: rest = out := by simpa [decodeAtoms,head,tail] using h
                subst out
                exact .cons ((exactRow ops a t).mp head) ((ih rest).mp tail)
      · intro h
        cases h with
        | cons one more =>
            simp [decodeAtoms,(exactRow ops _ _).mpr one,(ih _).mpr more]

private theorem atomNames (p : NormalForm.Formula) (a : NormalForm.Atom) (ha : a ∈ LinearRows.atoms p)
    (t : Summand) (ht : t ∈ a.row.2) : t.2.name ∈ p.variables := by
  induction p with
  | truth => cases ha
  | falsity => cases ha
  | atom b =>
      have same := List.mem_singleton.mp ha
      subst a
      exact List.mem_map.mpr ⟨t,ht,rfl⟩
  | negative q ih => exact ih ha
  | conjunction l r hl hr =>
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_append_left _ (hl h)
      · exact List.mem_append_right _ (hr h)
  | disjunction l r hl hr =>
      rcases List.mem_append.mp ha with h | h
      · exact List.mem_append_left _ (hl h)
      · exact List.mem_append_right _ (hr h)

private theorem buildTerms (ops : List LowerOperand) (terms : List Summand)
    (fits : ∀ t ∈ terms, ∃ j : Nat, ∃ h : j < ops.length, t.2 = .variable (j+1)) :
    ∃ out : List WeightedOperand, List.Forall₂ (LiteralTerm ops) terms out := by
  induction terms with
  | nil => exact ⟨[],.nil⟩
  | cons t rest ih =>
      obtain ⟨j,h,eq⟩ := fits t List.mem_cons_self
      obtain ⟨out,shape⟩ := ih (fun u hu => fits u (List.mem_cons_of_mem _ hu))
      exact ⟨(t.1,ops[j]) :: out,.cons ⟨j,h,eq,rfl⟩ shape⟩

private theorem buildAtoms (ops : List LowerOperand) (atoms : List NormalForm.Atom)
    (fits : ∀ a ∈ atoms, ∀ t ∈ a.row.2, ∃ j : Nat, ∃ h : j < ops.length, t.2 = .variable (j+1)) :
    ∃ out : List Row, List.Forall₂ (LiteralRow ops) atoms out := by
  induction atoms with
  | nil => exact ⟨[],.nil⟩
  | cons a rest ih =>
      obtain ⟨terms,shape⟩ := buildTerms ops a.row.2 (fits a List.mem_cons_self)
      obtain ⟨rows,later⟩ := ih (fun b hb => fits b (List.mem_cons_of_mem _ hb))
      exact ⟨(testOf a,a.row.1,terms) :: rows,.cons ⟨rfl,rfl,shape⟩ later⟩

theorem exactProjectedMatrixDecode : ExactProjectedMatrixDecode := by
  refine ⟨exactTerm,fun ops p rows => exactAtoms ops (LinearRows.atoms p) rows,?_⟩
  intro ops p fits
  have atomFit (a : NormalForm.Atom) (ha : a ∈ LinearRows.atoms p) (t : Summand) (ht : t ∈ a.row.2) :
      ∃ j : Nat, ∃ h : j < ops.length, t.2 = .variable (j+1) := by
    obtain ⟨n,eq⟩ := fits.1.1 a ha t ht
    have listed := atomNames p a ha t ht
    rw [eq] at listed
    have bound := fits.1.2 n listed
    have positive := fits.2 n listed
    cases n with
    | zero => exact (Nat.lt_irrefl 0 positive).elim
    | succ j => exact ⟨j,Nat.lt_of_succ_le bound,eq⟩
  obtain ⟨out,cal⟩ := buildAtoms ops (LinearRows.atoms p) atomFit
  exact ⟨out,(exactAtoms ops _ _).mpr cal⟩

end LogicLineages.PermittedControl.OriginalProjectedMatrixDecode

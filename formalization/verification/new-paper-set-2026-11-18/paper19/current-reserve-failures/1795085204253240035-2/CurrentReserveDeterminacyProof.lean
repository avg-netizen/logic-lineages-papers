module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveAlgebraProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open ActiveScalarAnnotation

theorem forgetOrigins {p f k Γ} {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs : List (Carrier p)} {c : Nat} (h : SpawnedAccount p f q xs c) : Account p f q xs c := by
  induction h with
  | free hn => exact .free hn
  | tracked => exact .tracked
  | add ha _ _ ih ih' => exact .add ha ih ih'
  | finite ha he _ ih => exact .finite ha he ih
  | nonfinite a ha hn he _ _ ih =>
    exact .nonfinite a ha hn he (fun h => by cases h) ih

private theorem finiteNonfiniteFalse {a : Ordinal} {n : Nat}
    (hf : a = (n : Ordinal)) (hn : Ordinal.omega0 ≤ a) : False := by
  rw [hf] at hn
  exact (not_le_of_gt (Ordinal.natCast_lt_omega0 n)) hn

noncomputable def headValues {p} (f : Nat → Nat) (xs : List (Carrier p)) : List Ordinal :=
  xs.map (Carrier.head f)

theorem accountHeadsConstant {p f k Γ}
    {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs ys : List (Carrier p)} {c d : Nat}
    (hx : Account p f q xs c) (hy : Account p f q ys d) :
    headValues f xs = headValues f ys ∧ c = d := by
  induction hx generalizing ys d with
  | free hn =>
    cases hy with
    | free _ => exact ⟨rfl,rfl⟩
    | tracked => exact False.elim (hn trackedActive)
    | add ha _ _ => exact False.elim (hn ha)
    | finite ha _ _ => exact False.elim (hn ha)
    | nonfinite _ ha _ _ _ _ => exact False.elim (hn ha)
  | tracked =>
    cases hy with
    | free hn => exact False.elim (hn trackedActive)
    | tracked => exact ⟨rfl,rfl⟩
  | add ha left right ihl ihr =>
    cases hy with
    | free hn => exact False.elim (hn ha)
    | add _ left' right' =>
      obtain ⟨hl,hc⟩ := ihl left'
      obtain ⟨hr,hd⟩ := ihr right'
      refine ⟨?_,by omega⟩
      simpa only [headValues,List.map_append] using congrArg₂ (fun (xs ys : List Ordinal) => xs++ys) hl hr
  | @finite h t xs c n ha hf tail ih =>
    cases hy with
    | free hn => exact False.elim (hn ha)
    | @finite _ _ ys d m _ hf' tail' =>
      obtain ⟨hh,hc⟩ := ih tail'
      have hnm : n=m := by exact_mod_cast hf.symm.trans hf'
      exact ⟨hh,by omega⟩
    | nonfinite _ _ hnf _ _ _ => exact False.elim (finiteNonfiniteFalse hf hnf)
  | @nonfinite h t xs c a ha hn he _ tail ih =>
    cases hy with
    | free hb => exact False.elim (hb ha)
    | finite _ hf _ => exact False.elim (finiteNonfiniteFalse hf hn)
    | nonfinite b _ _ he' _ tail' =>
      obtain ⟨hh,hc⟩ := ih tail'
      have hl : a.head f = b.head f := he.trans he'.symm
      refine ⟨?_,by omega⟩
      simpa only [headValues,List.map_append,List.map_cons,List.map_nil] using
        congrArg₂ (fun (xs ys : List Ordinal) => xs++ys) hh (congrArg (fun x : Ordinal => [x]) hl)

theorem reserveDeterminacy {p f k Γ}
    {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs ys : List (Carrier p)} {c d : Nat}
    (hx : Account p f q xs c) (hy : Account p f q ys d) : reserve xs c = reserve ys d := by
  obtain ⟨hh,hc⟩ := accountHeadsConstant hx hy
  have hl : xs.length = ys.length := by
    simpa only [headValues,List.length_map] using congrArg List.length hh
  simp only [reserve,hc,hl]

theorem inactiveData {p f k Γ} {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs : List (Carrier p)} {c : Nat} (hx : Account p f q xs c)
    (hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
    xs=[] ∧ c=1 := by
  obtain ⟨hh,hc⟩ := accountHeadsConstant hx (.free hn)
  have hl : xs.length = 0 := by
    simpa only [headValues,List.length_map,List.length_nil] using congrArg List.length hh
  exact ⟨List.length_eq_zero_iff.mp hl,hc⟩

theorem inactiveReserve {p f k Γ} {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs : List (Carrier p)} {c : Nat} (hx : Account p f q xs c)
    (hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
    reserve xs c = 1 := by
  obtain ⟨rfl,rfl⟩ := inactiveData hx hn
  rfl

end LogicLineages.ControlSensitivityCurrent.CurrentReserve

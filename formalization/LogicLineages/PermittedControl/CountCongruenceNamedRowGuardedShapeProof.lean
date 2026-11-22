module
public import LogicLineages.PermittedControl.CountCongruenceNamedRowGuardedAggregateTargets
import LogicLineages.PermittedControl.ShortFieldGapProof

@[expose] public section
namespace LogicLineages.PermittedControl.CountCongruenceNamedRow
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private def rowFrom (m k nmu : Nat) (c u v : Int) (js : List Nat) : NormalForm.Formula :=
  js.foldr (fun j tail => if keepResidue m k nmu j c u v then
    .disjunction (residueAtom m j) tail else tail) .falsity

private theorem zeroGapLong (lam mu : NONote) (hp : ProperField (.entry 0 lam mu)) :
    shortGapLength lam mu = 0 ↔ LongField (.entry 0 lam mu) := by
  constructor
  · intro hz
    refine ⟨hp.1,hp.2.1,hp.2.2,?_⟩
    rintro ⟨k,hk,hend⟩
    exact (Nat.ne_of_gt hk) (((shortGapRecognition lam mu hp k hk).2.2.mpr hend).symm.trans hz)
  · intro hl
    rcases Nat.eq_zero_or_pos (shortGapLength lam mu) with hz | hk
    · exact hz
    · exact (hl.2.2.2 ⟨_,hk,(shortGapRecognition lam mu hp _ hk).2.2.mp rfl⟩).elim

private theorem rowFromPlain (m k nmu : Nat) (c u v : Int) (js : List Nat) :
    PlainPreparedFormula (rowFrom m k nmu c u v js) := by
  induction js with
  | nil => simp [PlainPreparedFormula,rowFrom,LinearRows.atoms]
  | cons j js ih =>
    by_cases h : keepResidue m k nmu j c u v = true
    · intro a ha s hs
      have ha' : a = .divisible (2*m-1) (-(j : Int),[(1,.variable 1)]) ∨
          a ∈ LinearRows.atoms (rowFrom m k nmu c u v js) := by
        simpa only [rowFrom,List.foldr_cons,if_pos h,residueAtom,LinearRows.atoms,
          List.singleton_append,List.mem_cons] using ha
      rcases ha' with he | ht
      · subst a
        have he : s = (1,.variable 1) := List.mem_singleton.mp hs
        subst s
        exact ⟨1,rfl⟩
      · exact ih a ht s hs
    · simpa only [rowFrom,List.foldr_cons,if_neg h] using ih

private theorem rowFromSupport (m k nmu : Nat) (c u v : Int) (js : List Nat) :
    ∀ i ∈ (rowFrom m k nmu c u v js).variables, i = 1 := by
  induction js with
  | nil => simp [rowFrom,NormalForm.Formula.variables]
  | cons j js ih =>
    intro i hi
    by_cases h : keepResidue m k nmu j c u v = true
    · have hi' : i = 1 ∨ i ∈ (rowFrom m k nmu c u v js).variables := by
        simpa only [rowFrom,List.foldr_cons,if_pos h,residueAtom,NormalForm.Formula.variables,
          NormalForm.Atom.row,NormalForm.rowVariables,List.map_cons,List.map_nil,
          NormalForm.Summand.name,List.singleton_append,List.mem_cons] using hi
      exact hi'.elim id (ih i)
    · apply ih i
      simpa only [rowFrom,List.foldr_cons,if_neg h] using hi

theorem guardedShapeAndSupport : ShapeAndSupport := by
  constructor
  · intro lam mu hp
    exact ⟨zeroGapLong lam mu hp,fun k hk => (shortGapRecognition lam mu hp k hk).2.2⟩
  · intro m rank k nmu c u v
    refine ⟨rowFromPlain m k nmu c u v (List.range (2*m)),?_,?_,?_⟩
    · simp [requests]
    · simp [requests]
    · intro i hi
      have he := rowFromSupport m k nmu c u v (List.range (2*m)) i hi
      simp [requests,he]

end LogicLineages.PermittedControl.CountCongruenceNamedRow

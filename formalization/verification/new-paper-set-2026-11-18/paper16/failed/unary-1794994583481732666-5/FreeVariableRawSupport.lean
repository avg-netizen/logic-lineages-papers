import LogicLineages.PersistentMarking.FreeVariableTargets
namespace LogicLineages.PersistentMarking.FreeVariableRawSupport
open Spine NameBridge

theorem consParts {name : Name} {q : Expr} {qs : Args} (h : freeOccursArgs name (.cons q qs) = false) :
    freeOccurs name q = false ∧ freeOccursArgs name qs = false := by
  simpa only [freeOccursArgs,Bool.or_eq_false_iff] using h

theorem markedParts {name : Name} {f : Head} {τ : Ty} {base extras : Args}
    (h : freeOccurs name (.marked f τ base extras) = false) :
    freeOccursArgs name base = false ∧ freeOccursArgs name extras = false := by
  simpa only [freeOccurs,Bool.or_eq_false_iff] using h

theorem consAbsent {name : Name} {q : Expr} {qs : Args}
    (hq : freeOccurs name q = false) (hqs : freeOccursArgs name qs = false) :
    freeOccursArgs name (.cons q qs) = false := by simp only [freeOccursArgs,hq,hqs,Bool.or_self]

theorem markedAbsent {name : Name} {f : Head} {τ : Ty} {base extras : Args}
    (hb : freeOccursArgs name base = false) (he : freeOccursArgs name extras = false) :
    freeOccurs name (.marked f τ base extras) = false := by simp only [freeOccurs,hb,he,Bool.or_self]

mutual
 theorem shiftNames (name : Name) (k d : Nat) (q : Expr) : freeOccurs name (shift k d q) = freeOccurs name q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ body => exact shiftNames name k (d+1) body
  | head f base => exact shiftArgsNames name k d base
  | marked f τ base extras => simp only [shift,freeOccurs,shiftArgsNames]
 termination_by sizeOf q
 theorem shiftArgsNames (name : Name) (k d : Nat) (qs : Args) : freeOccursArgs name (shiftArgs k d qs) = freeOccursArgs name qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,freeOccursArgs,shiftNames,shiftArgsNames]
 termination_by sizeOf qs
end

theorem getAbsent (name : Name) (qs : Args) (i : Nat) (q : Expr)
    (hq : qs.get i = some q) (h : freeOccursArgs name qs = false) : freeOccurs name q = false := by
  cases qs with
  | nil => simp [Args.get] at hq
  | cons a rest =>
    cases i with
    | zero => have he : a = q := Option.some.inj hq; subst q; exact (consParts h).1
    | succ i => exact getAbsent name rest i q hq (consParts h).2
termination_by sizeOf qs

theorem appendAbsent (name : Name) (xs ys : Args)
    (hx : freeOccursArgs name xs = false) (hy : freeOccursArgs name ys = false) :
    freeOccursArgs name (xs.append ys) = false := by
  cases xs with
  | nil => exact hy
  | cons q qs => exact consAbsent (consParts hx).1 (appendAbsent name qs ys (consParts hx).2 hy)
termination_by sizeOf xs

mutual
 theorem substituteAbsent (name : Name) (values : Args) (depth : Nat) (q : Expr)
    (hq : freeOccurs name q = false) (hv : freeOccursArgs name values = false) :
    freeOccurs name (substitute values depth q) = false := by
  cases q with
  | free σ x => exact hq
  | bound σ i =>
    by_cases hi : i < depth
    · simp only [substitute,hi,if_true,freeOccurs]
    · cases hg : values.get (i-depth) with
      | none => simp only [substitute,hi,if_false,hg,freeOccurs]
      | some v => simpa only [substitute,hi,if_false,hg,shiftNames] using getAbsent name values (i-depth) v hg hv
  | lam σ body => exact substituteAbsent name values (depth+1) body hq hv
  | head f base => exact substituteArgsAbsent name values depth base hq hv
  | marked f τ base extras =>
    exact markedAbsent (substituteArgsAbsent name values depth base (markedParts hq).1 hv)
      (substituteArgsAbsent name values depth extras (markedParts hq).2 hv)
 termination_by sizeOf q
 theorem substituteArgsAbsent (name : Name) (values : Args) (depth : Nat) (qs : Args)
    (hq : freeOccursArgs name qs = false) (hv : freeOccursArgs name values = false) :
    freeOccursArgs name (substituteArgs values depth qs) = false := by
  cases qs with
  | nil => rfl
  | cons q qs => exact consAbsent (substituteAbsent name values depth q (consParts hq).1 hv)
      (substituteArgsAbsent name values depth qs (consParts hq).2 hv)
 termination_by sizeOf qs
end

mutual
 theorem substituteReflects (name : Name) (values : Args) (depth : Nat) (q : Expr)
    (h : freeOccurs name (substitute values depth q) = false) : freeOccurs name q = false := by
  cases q with
  | free σ x => exact h
  | bound σ i => rfl
  | lam σ body => exact substituteReflects name values (depth+1) body h
  | head f base => exact substituteArgsReflects name values depth base h
  | marked f τ base extras => exact markedAbsent
      (substituteArgsReflects name values depth base (markedParts h).1)
      (substituteArgsReflects name values depth extras (markedParts h).2)
 termination_by sizeOf q
 theorem substituteArgsReflects (name : Name) (values : Args) (depth : Nat) (qs : Args)
    (h : freeOccursArgs name (substituteArgs values depth qs) = false) : freeOccursArgs name qs = false := by
  cases qs with
  | nil => rfl
  | cons q qs => exact consAbsent (substituteReflects name values depth q (consParts h).1)
      (substituteArgsReflects name values depth qs (consParts h).2)
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.FreeVariableRawSupport

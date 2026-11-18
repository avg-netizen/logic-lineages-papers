import LogicLineages.PersistentMarking.FreeVariableRawSupport
namespace LogicLineages.PersistentMarking.FreeVariableApplicationProof
open Spine NameBridge FreeVariableRawSupport

theorem auxiliary (name : Name) (q : Expr) (args values : Args) (r : Expr)
    (hq : freeOccurs name q = false) (ha : freeOccursArgs name args = false)
    (hv : freeOccursArgs name values = false) (hr : applyAux q args values = some r) :
    freeOccurs name r = false := by
  cases args with
  | nil =>
    have he : substitute values 0 q = r := by simpa only [applyAux,Option.some.injEq] using hr
    subst r
    exact substituteAbsent name values 0 q hq hv
  | cons a rest =>
    cases q with
    | free σ x => simp [applyAux] at hr
    | bound σ i => simp [applyAux] at hr
    | lam σ body =>
      by_cases he : a.type = σ
      · have hcall : applyAux body rest (.cons a values) = some r := by simpa only [applyAux,he,if_true] using hr
        exact auxiliary name body rest (.cons a values) r hq (consParts ha).2 (consAbsent (consParts ha).1 hv) hcall
      · simp [applyAux,he] at hr
    | head f base =>
      cases hc : consumeTypes f.result (.cons a rest) with
      | none => simp [applyAux,hc] at hr
      | some τ =>
        have he : Expr.marked f τ (substituteArgs values 0 base) (.cons a rest) = r := by
          simpa only [applyAux,hc,Option.map_some,Option.some.injEq] using hr
        subst r
        exact markedAbsent (substituteArgsAbsent name values 0 base hq hv) ha
    | marked f σ base extras =>
      cases hc : consumeTypes σ (.cons a rest) with
      | none => simp [applyAux,hc] at hr
      | some τ =>
        have he : Expr.marked f τ (substituteArgs values 0 base) ((substituteArgs values 0 extras).append (.cons a rest)) = r := by
          simpa only [applyAux,hc,Option.map_some,Option.some.injEq] using hr
        subst r
        exact markedAbsent (substituteArgsAbsent name values 0 base (markedParts hq).1 hv)
          (appendAbsent name _ _ (substituteArgsAbsent name values 0 extras (markedParts hq).2 hv) ha)
termination_by sizeOf args

theorem successfulApplicationAbsence : FreeVariableTargets.SuccessfulApplicationAbsence := by
  intro name q args r hq ha hr
  cases args with
  | nil => have he : q = r := Option.some.inj hr; subst r; exact hq
  | cons a rest => exact auxiliary name q (.cons a rest) .nil r hq ha rfl hr
end LogicLineages.PersistentMarking.FreeVariableApplicationProof

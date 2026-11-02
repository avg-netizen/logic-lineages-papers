module
public import LogicLineages.OrdinalComparison.AccountSemanticDeterminacyTargets
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy.Proof
open ScalarCarrierAccounting ActiveScalarAnnotation

private theorem tracked_active {k Γ} :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
      (.var ⟨_,.here,0⟩) := by
  simp [Active, AssignmentSupport.names, ordinalExpressionVariables, AssignmentSupport.componentName]

private theorem finite_nonfinite_false {a : Ordinal} {n : Nat}
    (hf : a = (n : Ordinal)) (hn : Ordinal.omega0 ≤ a) : False := by
  rw [hf] at hn
  exact (not_le_of_gt (Ordinal.natCast_lt_omega0 n)) hn

theorem account_heads_constant {k Γ}
    {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs ys : List Carrier} {c d : Nat}
    (hx : Account q xs c) (hy : Account q ys d) :
    headValues xs = headValues ys ∧ c = d := by
  induction hx generalizing ys d with
  | free inactive =>
    cases hy with
    | free _ => exact ⟨rfl,rfl⟩
    | tracked => exact False.elim (inactive tracked_active)
    | add active _ _ => exact False.elim (inactive active)
    | finite active _ _ => exact False.elim (inactive active)
    | nonfinite _ active _ _ _ => exact False.elim (inactive active)
  | tracked =>
    cases hy with
    | free inactive => exact False.elim (inactive tracked_active)
    | tracked => exact ⟨rfl,rfl⟩
  | add active left right ihl ihr =>
    cases hy with
    | free inactive => exact False.elim (inactive active)
    | add active' left' right' =>
      obtain ⟨hl,hc⟩ := ihl left'
      obtain ⟨hr,hd⟩ := ihr right'
      refine ⟨?_,by omega⟩
      simpa only [headValues, List.map_append] using congrArg₂ (fun (xs ys : List Ordinal) => xs ++ ys) hl hr
  | @finite h t xs c n active finite tail ih =>
    cases hy with
    | free inactive => exact False.elim (inactive active)
    | @finite _ _ ys d m active' finite' tail' =>
      obtain ⟨hh,hc⟩ := ih tail'
      have hnm : n = m := by exact_mod_cast (finite.symm.trans finite')
      exact ⟨hh,by omega⟩
    | nonfinite label active' nonfinite _ tail' =>
      exact False.elim (finite_nonfinite_false finite nonfinite)
  | @nonfinite h t xs c label active nonfinite exactHead tail ih =>
    cases hy with
    | free inactive => exact False.elim (inactive active)
    | finite active' finite tail' => exact False.elim (finite_nonfinite_false finite nonfinite)
    | nonfinite label' active' nonfinite' exactHead' tail' =>
      obtain ⟨hh,hc⟩ := ih tail'
      have hl : label.head = label'.head := exactHead.trans exactHead'.symm
      refine ⟨?_,by omega⟩
      simpa only [headValues, List.map_append, List.map_cons, List.map_nil] using
        congrArg₂ (fun (xs ys : List Ordinal) => xs ++ ys) hh (congrArg (fun a : Ordinal => [a]) hl)

theorem accountingDeterminacy : Targets.AccountingDeterminacy := by
  intro k Γ q xs ys c d hx hy
  obtain ⟨hh,hc⟩ := account_heads_constant hx hy
  have hl : xs.length = ys.length := by
    simpa only [headValues, List.length_map] using congrArg List.length hh
  exact ⟨hh,hc,hl,by simp only [reserve,hc,hl]⟩

end LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy.Proof

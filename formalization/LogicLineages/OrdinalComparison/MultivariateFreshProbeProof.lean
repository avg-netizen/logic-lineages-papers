module
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeTargets
public import LogicLineages.OrdinalComparison.InterpretedCollectedProof
public import LogicLineages.OrdinalComparison.ProfileHeadProof
public import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateFreshProbe

private theorem coefficient_le_code (e : ONote) (c : PNat) (t : ONote) :
    (c : Nat)≤rawNoteEncode (.oadd e c t) := by
  have h1 := Nat.left_le_pair ((c : Nat)-1) (rawNoteEncode t)
  have h2 := Nat.right_le_pair (rawNoteEncode e) (Nat.pair ((c : Nat)-1) (rawNoteEncode t))
  have hc := c.pos
  simp only [rawNoteEncode]
  omega

private theorem variable_repr (cap i : Nat) :
    (positiveVariableHead cap i).1.repr=Ordinal.omega0*((cap+i+1 : Nat) : Ordinal) := by
  simp [positiveVariableHead,ONote.repr]

private theorem variable_limit (cap i : Nat) :
    Order.IsSuccLimit (positiveVariableHead cap i).1.repr := by
  rw [variable_repr]
  exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
    (by exact_mod_cast (show 0<cap+i+1 by omega))

private theorem variable_index (cap i : Nat) :
    positiveVariableHeadIndex cap (positiveVariableHead cap i)=some i := by
  have hp : cap<cap+i+1 := by omega
  have hs : (cap+i+1)-cap-1=i := by omega
  simp [positiveVariableHeadIndex,positiveVariableHead,hp,hs]

private theorem original_index (cap : Nat) (rho : NONote)
    (hc : rawNoteEncode rho.1≤cap) : positiveVariableHeadIndex cap rho=none := by
  rcases rho with ⟨r,hr⟩
  cases r with
  | zero => rfl
  | oadd e c t =>
    have hco : (c : Nat)≤cap := (coefficient_le_code e c t).trans hc
    simp [positiveVariableHeadIndex,not_lt_of_ge hco]

theorem head_source : Targets.PositiveVariableHeadSource := by
  refine ⟨?_,original_index,?_⟩
  · intro cap i
    refine ⟨variable_limit cap i,rawNotation_repr_lt_epsilonZero _,?_,variable_index cap i⟩
    have hc := coefficient_le_code 1 ⟨cap+i+1,by omega⟩ 0
    change cap+i+1≤rawNoteEncode (.oadd 1 ⟨cap+i+1,by omega⟩ 0) at hc
    change cap<rawNoteEncode (.oadd 1 ⟨cap+i+1,by omega⟩ 0)
    omega
  · intro cap i x
    exact (Nat.zero_le x).trans_lt ((actualFixedLimitProfileHeads _ (variable_limit cap i)).2 x)

private theorem add_left_bound (E F : MultivariatePositiveExpr) :
    multivariatePositiveEncode E≤multivariatePositiveEncode (.add E F) := by
  have hp := Nat.left_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
  simp only [multivariatePositiveEncode]
  omega

private theorem add_right_bound (E F : MultivariatePositiveExpr) :
    multivariatePositiveEncode F≤multivariatePositiveEncode (.add E F) := by
  have hp := Nat.right_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
  simp only [multivariatePositiveEncode]
  omega

private theorem head_code_bound (rho : NONote) (E : MultivariatePositiveExpr) :
    rawNoteEncode rho.1≤multivariatePositiveEncode (.head rho E) := by
  have hp := Nat.left_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
  simp only [multivariatePositiveEncode]
  omega

private theorem head_arg_bound (rho : NONote) (E : MultivariatePositiveExpr) :
    multivariatePositiveEncode E≤multivariatePositiveEncode (.head rho E) := by
  have hp := Nat.right_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
  simp only [multivariatePositiveEncode]
  omega

private theorem original_retraction (cap : Nat) (ρ : Nat → Nat) (rho : NONote)
    (hc : rawNoteEncode rho.1≤cap) (z : Nat) :
    positiveRetractedHead cap ρ rho z=actualProfileHead rho z := by
  simp [positiveRetractedHead,original_index cap rho hc]

private theorem retraction_agreement (cap : Nat) (ρ : Nat → Nat) (E : MultivariatePositiveExpr)
    (hc : multivariatePositiveEncode E≤cap) :
    PositiveClosedHeadAgreement (positiveRetractedHead cap ρ) (multivariatePositiveProbe cap E) := by
  induction E with
  | constant c => trivial
  | input i => exact ⟨True.intro,fun h => nomatch h⟩
  | add E F ihE ihF =>
    exact ⟨ihE ((add_left_bound E F).trans hc),ihF ((add_right_bound E F).trans hc)⟩
  | head rho E ih =>
    refine ⟨ih ((head_arg_bound rho E).trans hc),?_⟩
    intro _ z
    exact original_retraction cap ρ rho ((head_code_bound rho E).trans hc) z

private theorem interpreted_probe (cap : Nat) (ρ : Nat → Nat) (E : MultivariatePositiveExpr)
    (hc : multivariatePositiveEncode E≤cap) (x : Nat) :
    interpretedPositiveEval (positiveRetractedHead cap ρ) (multivariatePositiveProbe cap E) x=
      actualMultivariatePositiveEval E ρ := by
  induction E with
  | constant c => rfl
  | input i =>
    simp [multivariatePositiveProbe,interpretedPositiveEval,positiveRetractedHead,
      variable_index,actualMultivariatePositiveEval]
  | add E F ihE ihF =>
    exact congrArg₂ (·+·) (ihE ((add_left_bound E F).trans hc))
      (ihF ((add_right_bound E F).trans hc))
  | head rho E ih =>
    change positiveRetractedHead cap ρ rho _=actualProfileHead rho _
    rw [original_retraction cap ρ rho ((head_code_bound rho E).trans hc),
      ih ((head_arg_bound rho E).trans hc)]

private theorem probe_valid (d cap : Nat) (E : MultivariatePositiveExpr)
    (hv : multivariatePositiveValid d E) :
    fixedLimitProfileBelow epsilonZero (multivariatePositiveProbe cap E) := by
  induction E with
  | constant c => trivial
  | input i => exact ⟨variable_limit cap i,rawNotation_repr_lt_epsilonZero _,True.intro⟩
  | add E F ihE ihF => exact ⟨ihE hv.1,ihF hv.2⟩
  | head rho E ih => exact ⟨hv.1,hv.2.1,ih hv.2.2⟩

private theorem probe_value (cap x : Nat) (E : MultivariatePositiveExpr) :
    actualFixedLimitProfileEval (multivariatePositiveProbe cap E) x=
      actualMultivariatePositiveEval E (fun i => actualProfileHead (positiveVariableHead cap i) x) := by
  induction E with
  | constant c => rfl
  | input i => rfl
  | add E F ihE ihF => exact congrArg₂ (·+·) ihE ihF
  | head rho E ih => exact congrArg (actualProfileHead rho) ih

private theorem probe_heads (cap : Nat) (E : MultivariatePositiveExpr)
    (hc : multivariatePositiveEncode E≤cap) :
    positiveHeadsSatisfy (PositiveProbeHeadClosure cap) (multivariatePositiveProbe cap E) := by
  induction E with
  | constant c => trivial
  | input i =>
    refine ⟨Or.inr ?_,True.intro⟩
    simp [variable_index]
  | add E F ihE ihF =>
    exact ⟨ihE ((add_left_bound E F).trans hc),ihF ((add_right_bound E F).trans hc)⟩
  | head rho E ih =>
    exact ⟨Or.inl ((head_code_bound rho E).trans hc),ih ((head_arg_bound rho E).trans hc)⟩

theorem source : Targets.MultivariateFreshProbeSource := by
  refine ⟨probe_valid,probe_value,?_⟩
  intro cap E hc
  exact InterpretedCollected.head_closure _ _ (probe_heads cap E hc)

theorem retraction : Targets.MultivariateFreshProbeRetraction := by
  intro d cap E hv hc ρ x
  exact (InterpretedCollected.normalization (positiveRetractedHead cap ρ)
    (multivariatePositiveProbe cap E) (probe_valid d cap E hv)
    (retraction_agreement cap ρ E hc) x).trans (interpreted_probe cap ρ E hc x)

end LogicLineages.OrdinalComparison.MultivariateFreshProbe

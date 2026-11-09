module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitFrameProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearSemanticStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem linear_conjunction (i : Nat) (p q : Formula)
    (hp : PlainMaximum.linearIn i p = true) (hq : PlainMaximum.linearIn i q = true) :
    PlainMaximum.linearIn i (.conjunction p q) = true := by
  have hPairP := (Bool.and_eq_true_iff
    (x := !p.parameters.contains i)
    (y := (PlainMaximum.occurrences p).all (fun a => PlainMaximum.linearSummand i a.2))).mp hp
  have hPairQ := (Bool.and_eq_true_iff
    (x := !q.parameters.contains i)
    (y := (PlainMaximum.occurrences q).all (fun a => PlainMaximum.linearSummand i a.2))).mp hq
  have hP := hPairP.1
  have hA := hPairP.2
  have hQ := hPairQ.1
  have hB := hPairQ.2
  have hpi : i ∉ p.parameters := by simpa using hP
  have hqi : i ∉ q.parameters := by simpa using hQ
  have hno : i ∉ (Formula.conjunction p q).parameters := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hpi h
    · exact hqi h
  have htest : (!(Formula.conjunction p q).parameters.contains i) = true := by simpa using hno
  have hocc : (PlainMaximum.occurrences (.conjunction p q)).all
      (fun a => PlainMaximum.linearSummand i a.2) = true := by
    simp only [PlainMaximum.occurrences, List.all_append]
    exact (Bool.and_eq_true_iff
      (x := (PlainMaximum.occurrences p).all (fun a => PlainMaximum.linearSummand i a.2))
      (y := (PlainMaximum.occurrences q).all (fun a => PlainMaximum.linearSummand i a.2))).mpr ⟨hA, hB⟩
  exact (Bool.and_eq_true_iff
    (x := !(Formula.conjunction p q).parameters.contains i)
    (y := (PlainMaximum.occurrences (.conjunction p q)).all
      (fun a => PlainMaximum.linearSummand i a.2))).mpr ⟨htest, hocc⟩

theorem linear_disjunction (i : Nat) (p q : Formula)
    (hp : PlainMaximum.linearIn i p = true) (hq : PlainMaximum.linearIn i q = true) :
    PlainMaximum.linearIn i (.disjunction p q) = true :=
  linear_conjunction i p q hp hq

theorem linear_all (i : Nat) (ps : List Formula)
    (hps : ∀ p ∈ ps, PlainMaximum.linearIn i p = true) :
    PlainMaximum.linearIn i (all ps) = true := by
  induction ps with
  | nil => simp [all, PlainMaximum.linearIn, Formula.parameters, PlainMaximum.occurrences]
  | cons p ps ih =>
    exact linear_conjunction i p (all ps) (hps p List.mem_cons_self)
      (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)))

theorem lower_guard_linear (x i c : Nat) :
    PlainMaximum.linearIn x (lowerGuard i c) = true := by
  simp [lowerGuard, PlainMaximum.linearIn, Formula.parameters, Atom.row, Row.parameters,
    Term.variables, PlainMaximum.occurrences, PlainMaximum.linearSummand]

theorem strict_maximum_guard_linear (x i j : Nat) :
    PlainMaximum.linearIn x (strictMaximumGuard i j) = true := by
  simp [strictMaximumGuard, PlainMaximum.linearIn, Formula.parameters, Atom.row,
    Row.parameters, Term.variables, PlainMaximum.occurrences, PlainMaximum.linearSummand]

theorem frame_linear (x : Nat) (bound : List Nat) (i : Nat) (p : Formula) :
    PlainMaximum.linearIn x (frame bound i p) = true := by
  apply linear_conjunction
  · exact lower_guard_linear x i (cutoff p)
  · apply linear_all
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    exact strict_maximum_guard_linear x i j

theorem outside_row_parameter_support (i : Nat) (r : Row) (j : Nat)
    (hj : j ∈ (outsideRow i r).parameters) : j ∈ r.parameters := by
  by_cases hz : PlainMaximum.headCoefficient i r = 0
  · simp [outsideRow, hz, Formula.parameters] at hj
  · simp only [outsideRow, if_neg hz, Formula.parameters, Atom.row, Row.parameters,
      Term.variables, List.mem_append, List.not_mem_nil, or_false, false_or,
      PlainMaximumProof.boundary_support] at hj ⊢
    tauto

theorem outside_row_linear (i : Nat) (r : Row) (hi : i ∉ r.parameters) :
    PlainMaximum.linearIn i (outsideRow i r) = true := by
  have hno : i ∉ (outsideRow i r).parameters := fun h => hi (outside_row_parameter_support i r i h)
  have ht : (!(outsideRow i r).parameters.contains i) = true := by simpa using hno
  unfold PlainMaximum.linearIn
  rw [ht, Bool.true_and]
  by_cases hz : PlainMaximum.headCoefficient i r = 0 <;>
    simp [outsideRow, hz, PlainMaximum.occurrences, Atom.row, PlainMaximum.linearSummand]

theorem outside_linear (i : Nat) (p : Formula) (hi : i ∉ p.parameters) :
    PlainMaximum.linearIn i (outside i p) = true := by
  apply linear_all
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  cases a with
  | nonnegative r =>
    apply outside_row_linear
    intro h
    exact hi (atom_parameter_support p (.nonnegative r) ha i h)
  | divisible m r =>
    simp [PlainMaximum.linearIn, Formula.parameters, PlainMaximum.occurrences]

theorem linearize_linear (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound)
    (hallowed : TiedLinear.allowed bound p = true) (hparams : ParametersIndependent bound p) :
    PlainMaximum.linearIn i (linearize i p) = true := by
  induction p with
  | truth => simp [linearize, PlainMaximum.linearIn, Formula.parameters, PlainMaximum.occurrences]
  | falsity => simp [linearize, PlainMaximum.linearIn, Formula.parameters, PlainMaximum.occurrences]
  | atom a =>
    cases a with
    | nonnegative r =>
      exact PlainMaximumProof.exactEliminandLinearity bound r i hallowed (hparams i hi)
    | divisible m r =>
      exact PlainMaximumResidueProof.exactEliminandLinearity bound r m i hallowed (hparams i hi)
  | negative p ih => exact ih hallowed hparams
  | conjunction p q ihp ihq =>
    obtain ⟨hap, haq⟩ := Bool.and_eq_true_iff.mp hallowed
    apply linear_conjunction
    · exact ihp hap (fun j hj h => hparams j hj (List.mem_append_left _ h))
    · exact ihq haq (fun j hj h => hparams j hj (List.mem_append_right _ h))
  | disjunction p q ihp ihq =>
    obtain ⟨hap, haq⟩ := Bool.and_eq_true_iff.mp hallowed
    apply linear_disjunction
    · exact ihp hap (fun j hj h => hparams j hj (List.mem_append_left _ h))
    · exact ihq haq (fun j hj h => hparams j hj (List.mem_append_right _ h))

/-- The literal guarded outside branch really passes the existing Cooper
kernel's SOURCE syntactic linearity test at the selected original name. -/
theorem far_input_linear (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound)
    (hallowed : TiedLinear.allowed bound p = true) (hparams : ParametersIndependent bound p) :
    PlainMaximum.linearIn i
      (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p))) = true := by
  apply linear_conjunction
  · exact frame_linear i bound i p
  · exact linear_conjunction i _ _ (outside_linear i p (hparams i hi))
      (linearize_linear bound p i hi hallowed hparams)

private theorem transport_actual_elimination (i : Nat) (q : Formula) (ν : Nat → Nat)
    (hlinear : PlainMaximum.linearIn i q = true) (P : Nat → Prop)
    (hbody : ∀ n : Nat, q.eval (Function.update ν i n) ↔ P n) :
    (TiedLinear.eliminate i q).eval ν ↔ ∃ n : Nat, P n :=
  (TiedLinearProof.actualTiedLinearElimination i q hlinear ν).trans (exists_congr hbody)

/-- Genuine parameter-preserving natural projection of the entire guarded
outside case. Its scalar guards and source linearity are derived internally;
only the selected ORIGINAL natural name is quantified by Cooper. -/
theorem far_branch_meaning (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound)
    (hallowed : TiedLinear.allowed bound p = true) (hparams : ParametersIndependent bound p)
    (ν : Nat → Nat) :
    (TiedLinear.eliminate i
      (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))).eval ν ↔
        ∃ n : Nat, (frame bound i p).eval (Function.update ν i n) ∧
          (outside i p).eval (Function.update ν i n) ∧ p.eval (Function.update ν i n) := by
  refine transport_actual_elimination i
    (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))
    ν (far_input_linear bound p i hi hallowed hparams)
    (fun n => (frame bound i p).eval (Function.update ν i n) ∧
      (outside i p).eval (Function.update ν i n) ∧ p.eval (Function.update ν i n)) ?_
  intro n
  change ((frame bound i p).eval (Function.update ν i n) ∧
    (outside i p).eval (Function.update ν i n) ∧
    (linearize i p).eval (Function.update ν i n)) ↔ _
  constructor
  · rintro ⟨hframe, hout, hlin⟩
    exact ⟨hframe, hout,
      (linearize_under_frame bound p i (Function.update ν i n) hi hallowed hparams hframe hout).mp hlin⟩
  · rintro ⟨hframe, hout, hp⟩
    exact ⟨hframe, hout,
      (linearize_under_frame bound p i (Function.update ν i n) hi hallowed hparams hframe hout).mpr hp⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof

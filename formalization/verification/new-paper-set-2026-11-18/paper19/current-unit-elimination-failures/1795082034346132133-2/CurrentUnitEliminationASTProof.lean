module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationTargets
public import LogicLineages.ControlSensitivityCurrent.SourceASTObservationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open CurrentOneUnit

theorem termEvalRename (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ Δ : List Ty} (r : Renaming Γ Δ) (ν : Variable Δ .ground → Nat)
    (t : SourceAST.Term Γ) :
    (renameTerm r t).eval p f ν = t.eval p f (fun x => ν (r x)) := by
  induction t with
  | var x => rfl
  | literal n => rfl
  | add a b ia ib => simp only [renameTerm,SourceAST.Term.eval,ia,ib]
  | unary h a ia => simp only [renameTerm,SourceAST.Term.eval,ia]
  | observation a => exact SourceAST.sourceValue_rename p f r (fun x => ν (r x)) ν (fun _ => rfl) a

theorem formulaEvalRename (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ Δ : List Ty} (r : Renaming Γ Δ) (ν : Variable Δ .ground → Nat)
    (a : SourceAST.Formula Γ) :
    (renameFormula r a).eval p f ν = a.eval p f (fun x => ν (r x)) := by
  induction a <;> simp only [renameFormula,SourceAST.Formula.eval,termEvalRename,*]

theorem evalTimes (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ω : Variable Γ .ground → Nat) (d : Nat) (t : SourceAST.Term Γ) :
    (times d t).eval p f ω = d * t.eval p f ω := by
  induction d with
  | zero => simp only [times,SourceAST.Term.eval,Nat.zero_mul]
  | succ d ih => simp only [times,SourceAST.Term.eval,ih,Nat.succ_mul,Nat.add_comm]

theorem evalRow (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ω : Variable Γ .ground → Nat) (row : LinearCode) (l l' z : SourceAST.Term Γ) :
    (rowFormula row l l' z).eval p f ω = true ↔
      holds row (l.eval p f ω) (l'.eval p f ω) (z.eval p f ω) := by
  simp only [rowFormula,SourceAST.Formula.eval,SourceAST.Term.eval,evalTimes,decide_eq_true_eq,holds]

theorem evalRaw (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ω : Variable Γ .ground → Nat) (x : Variable Γ .ground) :
    (raw x).eval p f ω = ω x + 1 := rfl

theorem termRetainsGrammar {Γ Δ : List Ty} (r : Renaming Γ Δ) (t : SourceAST.Term Γ)
    (ht : LinearTerm t) : LinearTerm (renameTerm r t) := by
  induction t <;> simp only [renameTerm,LinearTerm] at ht ⊢ <;> tauto

theorem formulaRetainsGrammar {Γ Δ : List Ty} (r : Renaming Γ Δ) (q : SourceAST.Formula Γ)
    (hq : Conjunctive q) : Conjunctive (renameFormula r q) := by
  induction q with
  | truth => exact trivial
  | falsity => exact hq
  | eq a b => exact ⟨termRetainsGrammar r a hq.1,termRetainsGrammar r b hq.2⟩
  | le a b => exact hq
  | lt a b => exact hq
  | neg a ia => exact hq
  | conj a b ia ib => exact ⟨ia hq.1,ib hq.2⟩
  | disj a b ia ib => exact hq

theorem timesLinear {Γ : List Ty} (n : Nat) (t : SourceAST.Term Γ) (ht : LinearTerm t) :
    LinearTerm (times n t) := by
  induction n with
  | zero => exact trivial
  | succ n ih => exact ⟨ht,ih⟩

theorem rawLinear {Γ : List Ty} (x : Variable Γ .ground) : LinearTerm (raw x) :=
  ⟨trivial,trivial⟩

theorem rowConjunctive {Γ : List Ty} (row : LinearCode) (l l' z : SourceAST.Term Γ)
    (hl : LinearTerm l) (hl' : LinearTerm l') (hz : LinearTerm z) :
    Conjunctive (rowFormula row l l' z) :=
  ⟨⟨timesLinear _ _ hl,trivial⟩,⟨⟨timesLinear _ _ hl',timesLinear _ _ hz⟩,trivial⟩⟩

private theorem pinExact (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
    {Δ : List Ty} (ω : Variable Δ .ground → Nat) (r : Variable Γ .ground → Variable Δ .ground)
    (ρ : Variable Γ .ground → Nat) :
    (pinGround Γ r ρ).eval p f ω = true ↔ ∀ (x : Variable Γ .ground), ω (r x) = ρ x := by
  induction Γ with
  | nil => exact ⟨fun _ x => nomatch x,fun _ => rfl⟩
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      simp only [pinGround,SourceAST.Formula.eval,SourceAST.Term.eval,Bool.and_eq_true,
        decide_eq_true_eq,ih]
      refine ⟨fun h x => ?_,fun h => ⟨h .here,fun x => h (.there x)⟩⟩
      cases x with
      | here => exact h.1
      | there x => exact h.2 x
    | arrow a b =>
      rw [pinGround,ih]
      refine ⟨fun h x => ?_,fun h x => h (.there x)⟩
      cases x with
      | there x => exact h x

private theorem castEvalExists (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ Δ : List Ty} (e : Γ = Δ) (m : SourceAST.Formula Γ) :
    (∃ ω : Variable Δ .ground → Nat, (e ▸ m : SourceAST.Formula Δ).eval p f ω = true) ↔
      (∃ ω : Variable Γ .ground → Nat, m.eval p f ω = true) := by
  cases e
  rfl

theorem exactClosedFiber : CurrentUnitEliminationTargets.ExactClosedFiber := by
  intro p f Γ q hg ρ n
  unfold closeFiber SourceAST.Sentence.holds
  dsimp only
  rw [castEvalExists]
  unfold OpenGraph.holds
  simp only [SourceAST.Formula.eval,SourceAST.Term.eval,Bool.and_eq_true,decide_eq_true_eq,pinExact]
  refine ⟨?_,?_⟩
  · rintro ⟨ω,hM,hN,hρ⟩
    exact ⟨ω,hρ,hN,hM⟩
  · rintro ⟨ω,hρ,hN,hM⟩
    exact ⟨ω,hM,hN,hρ⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

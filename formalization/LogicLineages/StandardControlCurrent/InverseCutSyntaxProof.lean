module
public import LogicLineages.StandardControlCurrent.InverseCutSyntaxTargets
public import LogicLineages.StandardControlCurrent.InverseCutProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutSyntaxProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion InverseCutSyntax

theorem term_agrees (t : Term) (ν ρ : Nat → Nat)
    (h : ∀ i ∈ t.variables, ν i = ρ i) : t.value ν = t.value ρ := by
  induction t with
  | numeral n => rfl
  | «variable» i => exact h i (by simp [Term.variables])
  | add a b ia ib | subtract a b ia ib =>
    simp only [Term.value, ia (fun i hi => h i (by simp [Term.variables, hi])),
      ib (fun i hi => h i (by simp [Term.variables, hi]))]
  | multiply c a ih => simp only [Term.value, ih h]
  | divide c a ih => simp only [Term.value, ih h]
  | phi a ih => simp only [Term.value, ih h]
  | hyper a ih => simp only [Term.value, ih h]
  | phiInverse a ih => simp only [Term.value, ih h]
  | hyperInverse a ih => simp only [Term.value, ih h]

theorem term_update (t : Term) (ν : Nat → Nat) (x n : Nat)
    (hx : x ∉ t.variables) : t.value (Function.update ν x n) = t.value ν := by
  apply term_agrees
  intro i hi
  have hix : i ≠ x := by intro he; subst i; exact hx hi
  simp [Function.update, hix]

theorem matrix_agrees (p : Matrix) (ν ρ : Nat → Nat)
    (h : ∀ i ∈ p.variables, ν i = ρ i) : p.eval ν ↔ p.eval ρ := by
  induction p with
  | truth | falsity => rfl
  | equal a b | less a b =>
    simp only [Matrix.eval, term_agrees a ν ρ (fun i hi => h i (by simp [Matrix.variables, hi])),
      term_agrees b ν ρ (fun i hi => h i (by simp [Matrix.variables, hi]))]
  | divisible m a => simp only [Matrix.eval, term_agrees a ν ρ h]
  | negative p ih => exact not_congr (ih h)
  | conjunction p q ip iq | disjunction p q ip iq =>
    simp only [Matrix.eval, ip (fun i hi => h i (by simp [Matrix.variables, hi])),
      iq (fun i hi => h i (by simp [Matrix.variables, hi]))]

theorem apply_value (h : Nat) (t : Term) (ν : Nat → Nat) :
    (apply h t).value ν = function h (t.value ν) := by
  by_cases hh : h = 0 <;> simp [apply, function, hh, Term.value]

theorem remainder_value (m : Nat) (a : Term) (ν : Nat → Nat) :
    (remainder m a).value ν = a.value ν % m := by
  have h := Nat.mod_add_div (a.value ν) m
  simp only [remainder, Term.value]
  omega

theorem next_value (m r : Nat) (a : Term) (ν : Nat → Nat) :
    (next m r a).value ν = InverseCut.residueNext (a.value ν) m r := by
  simp only [next, Term.value, remainder_value, InverseCut.residueNext]

theorem branch_value (h m r : Nat) (a b hi lower : Term) (ν : Nat → Nat) :
    (branch h m r a b hi lower).eval ν ↔
    InverseCut.residueNext (max (a.value ν) (lower.value ν)) m r ≤ b.value ν ∧
    function h (InverseCut.residueNext (max (a.value ν) (lower.value ν)) m r) ≤ hi.value ν := by
  simp only [branch, le, Matrix.eval, not_lt, next_value, apply_value]
  by_cases hl : lower.value ν ≤ a.value ν
  · simp [hl, max_eq_left hl, Nat.not_lt.mpr hl]
  · have ha : a.value ν < lower.value ν := by omega
    simp [hl, ha, max_eq_right ha.le]

def inverseFunction (h : Nat) : Nat → Nat :=
  if h = 0 then LayeredComparison.SnyatkovInverse.phiInverse
  else LayeredComparison.SnyatkovInverse.hyperInverse

theorem inverse_value (h : Nat) (t : Term) (ν : Nat → Nat) :
    (inverse h t).value ν = inverseFunction h (t.value ν) := by
  by_cases hh : h = 0 <;> simp [inverse, inverseFunction, hh, Term.value]

theorem compile_answer (h m r : Nat) (a b lo hi : Term) (ν : Nat → Nat) :
    (compile h m r a b lo hi).eval ν ↔
    InverseCut.answer (function h) (inverseFunction h)
      (a.value ν,b.value ν,lo.value ν,hi.value ν,m,r) = true := by
  by_cases hv : 0 < m ∧ r < m
  · simp only [compile, if_pos hv, Matrix.eval, le, not_lt, apply_value, Term.value,
      branch_value, inverse_value, InverseCut.answer, decide_eq_true_eq,
      InverseCut.candidate]
    unfold InverseCut.lowerIndex
    by_cases hl : lo.value ν ≤ function h 0
    · simp [hl, hv.1, hv.2, Nat.not_lt.mpr hl]
    · have hg : function h 0 < lo.value ν := by omega
      simp [hl, hg, hv.1, hv.2]
  · simp only [compile, if_neg hv, Matrix.eval, InverseCut.answer, decide_eq_true_eq]
    tauto

theorem compile_cut (h m r : Nat) (a b lo hi : Term) (ν : Nat → Nat) :
    (compile h m r a b lo hi).eval ν ↔
    0 < m ∧ r < m ∧ InverseCut.Cut (function h)
      (a.value ν,b.value ν,lo.value ν,hi.value ν,m,r) := by
  rw [compile_answer]
  by_cases hh : h = 0
  · simpa [function, inverseFunction, hh] using
      (InverseCutProof.elimination (a.value ν,b.value ν,lo.value ν,hi.value ν,m,r)).1
  · simpa [function, inverseFunction, hh] using
      (InverseCutProof.elimination (a.value ν,b.value ν,lo.value ν,hi.value ν,m,r)).2

theorem parameterElimination : InverseCutSyntaxTargets.ParameterElimination := by
  intro h m r x a b lo hi ν hx
  have ha : x ∉ a.variables := by intro h; exact hx (by simp [support,h])
  have hb : x ∉ b.variables := by intro h; exact hx (by simp [support,h])
  have hl : x ∉ lo.variables := by intro h; exact hx (by simp [support,h])
  have hh : x ∉ hi.variables := by intro h; exact hx (by simp [support,h])
  rw [compile_cut]
  simp only [BoundCut, InverseCut.Cut, term_update a ν x _ ha, term_update b ν x _ hb,
    term_update lo ν x _ hl, term_update hi ν x _ hh, Function.update_self]

theorem outputSupport : InverseCutSyntaxTargets.OutputSupport := by
  intro h m r a b lo hi i
  by_cases hv : 0 < m ∧ r < m
  · by_cases hh : h = 0 <;>
      simp [compile, hv, branch, le, next, remainder, apply, inverse, hh,
        Matrix.variables, Term.variables, support] <;> tauto
  · simp [compile, hv, Matrix.variables]

theorem updateAndNegation : InverseCutSyntaxTargets.UpdateAndNegation := by
  intro h m r x a b lo hi ν hx
  constructor
  · intro n
    apply matrix_agrees
    intro i hi'
    have hix : i ≠ x := by
      intro he; subst i
      exact hx (outputSupport h m r a b lo hi x hi')
    simp [Function.update, hix]
  · exact not_congr (parameterElimination h m r x a b lo hi ν hx)

theorem literalCode : InverseCutSyntaxTargets.LiteralCode := by
  intro h m r a b lo hi
  by_cases hv : 0 < m ∧ r < m <;> by_cases hh : h = 0 <;>
    simp [compileCode, compile, hv, branchCode, branch, nextCode, next,
      remainderCode, remainder, leCode, le, applyCode, apply, inverseCode, inverse,
      numeralCode, addCode, subCode, mulCode, divCode, lessCode, negCode,
      andCode, orCode, Term.encode, Matrix.encode, hh]

theorem invalid : InverseCutSyntaxTargets.Invalid := by
  intro h m r a b lo hi hn
  have hv : ¬ (0 < m ∧ r < m) := by omega
  simp [compile, hv]
end LogicLineages.StandardControlCurrent.InverseCutSyntaxProof

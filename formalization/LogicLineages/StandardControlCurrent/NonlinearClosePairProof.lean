module
public import LogicLineages.StandardControlCurrent.NonlinearClosePairTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeCalibrationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NonlinearClosePairProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearClosePair

theorem actualWidth : NonlinearClosePairTargets.ActualWidth := by
  intro C a b hlo hhi
  have hl : a ≤ b := Phi_strictMono.le_iff_le.mp hlo
  have hu := LayeredComparison.SnyatkovHyperCollision.Proof.actualCoefficientElimination b a C hhi.le
  exact ⟨hl, by omega⟩

theorem substitution : NonlinearClosePairTargets.SubstitutionSemantics :=
  ⟨WindowProof.term_substitution, WindowProof.matrix_substitution⟩

theorem guard_truth (x k C : Nat) (v : Term) (ν : Nat → Nat) :
    (guard x k C v).eval ν ↔
    Phi (v.value ν) ≤ Phi (ν x+k) ∧ Phi (ν x+k) < C*Phi (v.value ν) := by
  simp [NonlinearClosePair.guard, InverseCutSyntax.le, Matrix.eval, Term.value]

theorem branch_truth (x k C : Nat) (v : Term) (p : Matrix) (j : Nat) (ν : Nat → Nat) :
    (branch x k C v p j).eval ν ↔
    k ≤ v.value ν+j ∧ (Matrix.conjunction (guard x k C v) p).eval
      (Function.update ν x (v.value ν+j-k)) := by
  simp only [branch, Matrix.eval, InverseCutSyntax.le, not_lt,
    WindowProof.matrix_substitution, candidate, Term.value]

theorem compile_truth (x k C : Nat) (v : Term) (p : Matrix) (ν : Nat → Nat) :
    (compile x k C v p).eval ν ↔ ∃ j : Nat, j < C+1 ∧
      k ≤ v.value ν+j ∧ (Matrix.conjunction (guard x k C v) p).eval
        (Function.update ν x (v.value ν+j-k)) := by
  rw [compile, WindowProof.any_truth]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨q,⟨j,hj,rfl⟩,hq⟩
    exact ⟨j,hj,(branch_truth x k C v p j ν).mp hq⟩
  · rintro ⟨j,hj,hq⟩
    exact ⟨_,⟨j,hj,rfl⟩,(branch_truth x k C v p j ν).mpr hq⟩

theorem parameterElimination : NonlinearClosePairTargets.ParameterElimination := by
  intro x k C v p ν hx
  rw [compile_truth]
  constructor
  · rintro ⟨j,hj,hk,h⟩
    exact ⟨_,h⟩
  · rintro ⟨n,h⟩
    have hg := (guard_truth x k C v _).mp h.1
    rw [WindowProof.term_update v x n ν hx] at hg
    simp only [Function.update_self] at hg
    have hw := actualWidth C (v.value ν) (n+k) hg.1 hg.2
    have he : v.value ν+(n+k-v.value ν)=n+k := by omega
    refine ⟨n+k-v.value ν,by omega,by omega,?_⟩
    rw [he, Nat.add_sub_cancel]
    exact h

theorem support : NonlinearClosePairTargets.Support := by
  intro x k C v p hx i hi
  rw [compile, WindowProof.any_support] at hi
  obtain ⟨q,hq,hi⟩ := hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  change i ∈ (InverseCutSyntax.le (.numeral k) (.add v (.numeral j))).variables ++
    ((Matrix.conjunction (guard x k C v) p).substitute x (candidate v k j)).variables at hi
  have hv (h : i ∈ v.variables) : i ≠ x ∧ (i ∈ v.variables ∨ i ∈ p.variables) :=
    ⟨by intro he; subst i; exact hx h, Or.inl h⟩
  rcases List.mem_append.mp hi with hi | hi
  · apply hv
    simpa [InverseCutSyntax.le, Matrix.variables, Term.variables] using hi
  · have hs := (WindowProof.matrix_support (Matrix.conjunction (guard x k C v) p)
      (candidate v k j) x i).mp hi
    rcases hs with ⟨hm,he⟩ | ⟨_,hr⟩
    · have hg : i ∈ (guard x k C v).variables → i=x ∨ i ∈ v.variables := by
        simp only [NonlinearClosePair.guard, InverseCutSyntax.le, Matrix.variables, Term.variables,
          List.mem_append, List.mem_singleton, List.not_mem_nil]
        tauto
      rcases List.mem_append.mp hm with hm | hm
      · rcases hg hm with hm | hm
        · exact False.elim (he hm)
        · exact hv hm
      · exact ⟨he,Or.inr hm⟩
    · apply hv
      simpa [candidate,Term.variables] using hr

theorem boundaryCases : NonlinearClosePairTargets.BoundaryCases := by
  intro x k v p ν
  have impossible (C : Nat) (hC : C ≤ 1) : ¬ (compile x k C v p).eval ν := by
    intro h
    obtain ⟨j,hj,hk,h⟩ := (compile_truth x k C v p ν).mp h
    have hg := (guard_truth x k C v _).mp h.1
    have hm := Nat.mul_le_mul_right (Phi (v.value (Function.update ν x (v.value ν+j-k)))) hC
    simp only [Nat.one_mul] at hm
    omega
  exact ⟨impossible 0 (by decide),impossible 1 le_rfl⟩

theorem guard_code (x k C : Nat) (v : Term) : guardCode x k C v.encode = (guard x k C v).encode := by
  simp [guardCode, NonlinearClosePair.guard, InverseCutSyntax.le, WindowCode.conjunction, WindowCode.atMost,
    WindowCode.negative, WindowCode.less, WindowCode.phi, WindowCode.add, WindowCode.var,
    WindowCode.numeral, WindowCode.multiply, Matrix.encode, Term.encode]

theorem candidate_code (v : Term) (k j : Nat) : candidateCode v.encode k j = (candidate v k j).encode := rfl

theorem branch_code (x k C : Nat) (v : Term) (p : Matrix) (j : Nat) :
    branchCode x k C v.encode p.encode j = (branch x k C v p j).encode := by
  unfold branchCode
  rw [candidate_code,guard_code]
  change WindowCode.conjunction _ (WindowCode.matrixSubstitute x (candidate v k j).encode
    (Matrix.conjunction (guard x k C v) p).encode) = _
  rw [WindowCodeProof.matrix_calibration]
  rfl

theorem any_code (xs : List Matrix) : WindowCode.any (xs.map Matrix.encode) = (Matrix.any xs).encode := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change 8*Nat.pair p.encode (WindowCode.any (ps.map Matrix.encode))+7 =
      8*Nat.pair p.encode (Matrix.any ps).encode+7
    rw [ih]

theorem literalCode : NonlinearClosePairTargets.LiteralCode := by
  intro x k C v p
  unfold program compile
  rw [← any_code]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact branch_code x k C v p j
end LogicLineages.StandardControlCurrent.NonlinearClosePairProof

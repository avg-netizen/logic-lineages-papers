module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecisionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision.Proof
open CotreePresburgerUnit

theorem quantifierEliminationExact : Targets.QuantifierEliminationExact := by
  intro n p
  induction p with
  | atom a => intro v; rfl
  | bot => intro v; simp [quantifierFree, evalQF, Boolean.eval, Realize]
  | neg p ih => intro v; simpa [quantifierFree, evalQF, Boolean.eval, Realize] using not_congr (ih v)
  | conj p q ihp ihq =>
    intro v
    simpa [quantifierFree, evalQF, Boolean.eval, Realize] using and_congr (ihp v) (ihq v)
  | ex p ih =>
    intro v
    rw [quantifierFree, CotreePresburgerNormalize.StatementChecks.eliminationExact]
    exact exists_congr (fun x => ih (Fin.snoc v (x : Int)))

theorem evaluationExact : Targets.EvaluationExact := quantifierEliminationExact

@[simp] theorem cast_snoc {n : Nat} (v : Fin n → Nat) (x : Nat) :
    (fun i : Fin (n + 1) => ((Fin.snoc (α := fun _ => Nat) v x i : Nat) : Int)) = Fin.snoc (fun i => (v i : Int)) (x : Int) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem closureExact : Targets.ClosureExact := by
  intro n
  induction n with
  | zero =>
    intro p
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      have he : (fun i : Fin 0 => (Fin.elim0 i : Nat) : Fin 0 → Nat) = Fin.elim0 := rfl
      have he' : (fun i : Fin 0 => ((Fin.elim0 i : Nat) : Int)) = Fin.elim0 := Subsingleton.elim _ _
      simpa only [close, he'] using h
    · rintro ⟨v,hv⟩
      have he : (fun i : Fin 0 => (v i : Int)) = Fin.elim0 := Subsingleton.elim _ _
      simpa only [close, he] using hv
  | succ n ih =>
    intro p
    rw [close, ih]
    change (∃ v : Fin n → Nat, ∃ x : Nat,
      Realize p (Fin.snoc (fun i => (v i : Int)) (x : Int))) ↔ _
    constructor
    · rintro ⟨v,x,h⟩
      exact ⟨Fin.snoc v x, by simpa only [cast_snoc] using h⟩
    · rintro ⟨v,h⟩
      refine ⟨Fin.init v, v (Fin.last n), ?_⟩
      rw [← cast_snoc, Fin.snoc_init_self]
      exact h

theorem satisfiabilityExact : Targets.SatisfiabilityExact := by
  intro n p
  rw [satisfiable, evaluationExact, closureExact]
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision.Proof

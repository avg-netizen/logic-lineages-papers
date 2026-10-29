module

public import LogicLineages.ComputabilityKnowledge.GorbowSubstitution

@[expose] public section

/-! Capture-avoiding simultaneous substitution for the fixed full source
formula language. The new variable introduced by a quantifier occupies index0;
old substitutions are shifted under it. This is an actual syntactic supplier,
not arithmetized representability, diagonalization or a theory axiom. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowFormulaSubstitution

open GorbowSyntax

def renameTerm {m n : Nat} (r : Fin m → Fin n) (t : Term m) : Term n :=
  GorbowSubstitution.substitute (fun i => .var (r i)) t

def liftSubstitute {m n : Nat} (σ : Fin m → Term n) : Fin (m + 1) → Term (n + 1) :=
  Fin.cases (.var 0) (fun i => renameTerm Fin.succ (σ i))

theorem liftSubstitute_realize {m n : Nat} (I : Interpretation)
    (v : Fin n → Nat) (x : Nat) (σ : Fin m → Term n) :
    (fun i => (liftSubstitute σ i).realize I (Fin.cases x v)) =
      Fin.cases x (fun i => (σ i).realize I v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact GorbowSubstitution.substitute_realize I (Fin.cases x v)
      (fun j => .var j.succ) (σ j)

def substituteFormula {m n : Nat} (σ : Fin m → Term n) : Formula m → Formula n
  | .equal t u => .equal (GorbowSubstitution.substitute σ t)
      (GorbowSubstitution.substitute σ u)
  | .universalRelation t => .universalRelation (GorbowSubstitution.substitute σ t)
  | .agent t => .agent (GorbowSubstitution.substitute σ t)
  | .knowledgeAll t => .knowledgeAll (GorbowSubstitution.substitute σ t)
  | .knowledge t u => .knowledge (GorbowSubstitution.substitute σ t)
      (GorbowSubstitution.substitute σ u)
  | .truth t => .truth (GorbowSubstitution.substitute σ t)
  | .neg φ => .neg (substituteFormula σ φ)
  | .imp φ ψ => .imp (substituteFormula σ φ) (substituteFormula σ ψ)
  | .conj φ ψ => .conj (substituteFormula σ φ) (substituteFormula σ ψ)
  | .disj φ ψ => .disj (substituteFormula σ φ) (substituteFormula σ ψ)
  | .all φ => .all (substituteFormula (liftSubstitute σ) φ)
  | .ex φ => .ex (substituteFormula (liftSubstitute σ) φ)

theorem substituteFormula_realize {m : Nat} (φ : Formula m) :
    ∀ {n : Nat} (I : Interpretation) (v : Fin n → Nat) (σ : Fin m → Term n),
      (substituteFormula σ φ).realize I v ↔
        φ.realize I (fun i => (σ i).realize I v) := by
  induction φ with
  | equal t u =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, GorbowSubstitution.substitute_realize]
  | universalRelation t =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, GorbowSubstitution.substitute_realize]
  | agent t =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, GorbowSubstitution.substitute_realize]
  | knowledgeAll t =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, GorbowSubstitution.substitute_realize]
  | knowledge t u =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, GorbowSubstitution.substitute_realize]
  | truth t =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, GorbowSubstitution.substitute_realize]
  | neg φ ih =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, ih]
  | imp φ ψ ihφ ihψ =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, ihφ, ihψ]
  | conj φ ψ ihφ ihψ =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    intro n I v σ
    simp only [substituteFormula, Formula.realize, ihφ, ihψ]
  | all φ ih =>
    intro n I v σ
    change (∀ x, (substituteFormula (liftSubstitute σ) φ).realize I (Fin.cases x v)) ↔ _
    apply forall_congr'
    intro x
    have h := ih I (Fin.cases x v) (liftSubstitute σ)
    rw [liftSubstitute_realize] at h
    exact h
  | ex φ ih =>
    intro n I v σ
    change (∃ x, (substituteFormula (liftSubstitute σ) φ).realize I (Fin.cases x v)) ↔ _
    apply exists_congr
    intro x
    have h := ih I (Fin.cases x v) (liftSubstitute σ)
    rw [liftSubstitute_realize] at h
    exact h

end LogicLineages.ComputabilityKnowledge.GorbowFormulaSubstitution

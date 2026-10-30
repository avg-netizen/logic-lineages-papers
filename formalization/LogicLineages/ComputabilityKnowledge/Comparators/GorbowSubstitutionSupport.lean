module

public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupport

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSubstitutionSupport
open GorbowSyntax GorbowFreeSupport GorbowFormulaSubstitution
open LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupport

def TermUses : Prop := ∀ m n (σ : Fin m → Term n) (t : Term m) (j : Fin n),
  (GorbowSubstitution.substitute σ t).uses j = true ↔ ∃ i : Fin m, t.uses i = true ∧ (σ i).uses j = true

def RenameUses : Prop := ∀ m n (r : Fin m → Fin n) (t : Term m) (j : Fin n),
  (renameTerm r t).uses j = true ↔ ∃ i : Fin m, t.uses i = true ∧ r i=j

def LiftUses : Prop := ∀ m n (σ : Fin m → Term n),
  (∀ i : Fin (m+1), (liftSubstitute σ i).uses 0 = true ↔ i=0) ∧
  (∀ (i : Fin (m+1)) (j : Fin n), (liftSubstitute σ i).uses j.succ = true ↔
    ∃ k : Fin m, i=k.succ ∧ (σ k).uses j = true)

def FormulaUses : Prop := ∀ m n (σ : Fin m → Term n) (φ : Formula m) (j : Fin n),
  (substituteFormula σ φ).uses j = true ↔ ∃ i : Fin m, φ.uses i = true ∧ (σ i).uses j = true

def ExactSupports : Prop := ∀ m n (σ : Fin m → Term n),
  (∀ t : Term m, termSupport (GorbowSubstitution.substitute σ t) = supportImage σ (termSupport t)) ∧
  (∀ φ : Formula m, formulaSupport (substituteFormula σ φ) = supportImage σ (formulaSupport φ))

def Target : Prop := TermUses ∧ RenameUses ∧ LiftUses ∧ FormulaUses ∧ ExactSupports
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSubstitutionSupport

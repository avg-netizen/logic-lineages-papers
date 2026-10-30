module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedBinding

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBinding
open GorbowSyntax GorbowFreeSupport GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowNamedBinding

def BindingSemantics : Prop := ∀ n (v : Fin n) (φ : Formula n) I ρ,
  ((bindAll v φ).realize I ρ ↔ ∀ x, φ.realize I (assignAt ρ v x)) ∧
  ((bindEx v φ).realize I ρ ↔ ∃ x, φ.realize I (assignAt ρ v x))

def BindingSupport : Prop := ∀ n (v : Fin n) (φ : Formula n),
  formulaSupport (bindAll v φ) = (formulaSupport φ).erase v.val ∧
  formulaSupport (bindEx v φ) = (formulaSupport φ).erase v.val

def SelectionSupport : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  formulaSupport (selectVariable v φ)={0} ∧ (selectVariable v φ).uses 0=true

def SelectionSemantics : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  ∀ I ρ, (selectVariable v φ).realize I (Fin.cases (ρ v) Fin.elim0) ↔ φ.realize I ρ

def QuantifierCalibration : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  ∀ I ρ,
    ((bindAll v φ).realize I ρ ↔ (Formula.all (selectVariable v φ)).realize I Fin.elim0) ∧
    ((bindEx v φ).realize I ρ ↔ (Formula.ex (selectVariable v φ)).realize I Fin.elim0)

def ClosedInstanceCalibration : Prop := ∀ n (v : Fin n) (φ : Formula n), formulaSupport φ={v.val} →
  ∀ (t : Term 0) I ρ,
    (instantiate (selectVariable v φ) t).realize I Fin.elim0 ↔
      φ.realize I (assignAt ρ v (t.realize I Fin.elim0))

def Target : Prop := BindingSemantics ∧ BindingSupport ∧ SelectionSupport ∧ SelectionSemantics ∧
  QuantifierCalibration ∧ ClosedInstanceCalibration
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBinding

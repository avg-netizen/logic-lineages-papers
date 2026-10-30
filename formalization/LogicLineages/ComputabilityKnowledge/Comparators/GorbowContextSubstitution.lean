module

public import LogicLineages.ComputabilityKnowledge.GorbowContextSubstitution

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowContextSubstitution
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaSubstitution GorbowContextTransport
open LogicLineages.ComputabilityKnowledge.GorbowContextSubstitution

def ShiftTransport : Prop := ∀ n m b (t : Term n) (u : Term m), term m t=some u →
  term (m+b) (GorbowTermShiftCode.shiftTerm b t)=some (GorbowTermShiftCode.shiftTerm b u)

def LiftCompatibility : Prop := ∀ n m k l (φ : Formula (n+1)) (ψ : Formula (m+1)),
  formula (m+1) φ=some ψ → ∀ (σ : Fin n → Term k) (τ : Fin m → Term l),
  Compatible (unbind (formulaSupport φ)) σ τ →
  Compatible (formulaSupport φ) (liftSubstitute σ) (liftSubstitute τ)

def TermSubstitution : Prop := ∀ n m k l (t : Term n) (u : Term m), term m t=some u →
  ∀ (σ : Fin n → Term k) (τ : Fin m → Term l), Compatible (termSupport t) σ τ →
    term l (GorbowSubstitution.substitute σ t)=some (GorbowSubstitution.substitute τ u)

def FormulaSubstitution : Prop := ∀ n m k l (φ : Formula n) (ψ : Formula m), formula m φ=some ψ →
  ∀ (σ : Fin n → Term k) (τ : Fin m → Term l), Compatible (formulaSupport φ) σ τ →
    formula l (substituteFormula σ φ)=some (substituteFormula τ ψ)

def NamedCommutation : Prop := ∀ n m (v : Fin n) (w : Fin m), v.val=w.val →
  ∀ (φ : Formula n) (ψ : Formula m), formula m φ=some ψ →
    formula m (bindAll v φ)=some (bindAll w ψ) ∧
    formula m (bindEx v φ)=some (bindEx w ψ) ∧ selectVariable v φ=selectVariable w ψ

def NamedEncoding : Prop := ∀ n m (v : Fin n) (w : Fin m), v.val=w.val →
  ∀ (φ : Formula n) (ψ : Formula m), formula m φ=some ψ →
    GorbowFormulaPrefixCode.encode (bindAll v φ)=GorbowFormulaPrefixCode.encode (bindAll w ψ) ∧
    GorbowFormulaPrefixCode.encode (bindEx v φ)=GorbowFormulaPrefixCode.encode (bindEx w ψ) ∧
    GorbowFormulaPrefixCode.encode (selectVariable v φ)=GorbowFormulaPrefixCode.encode (selectVariable w ψ)

def Target : Prop := ShiftTransport ∧ LiftCompatibility ∧ TermSubstitution ∧ FormulaSubstitution ∧ NamedCommutation ∧ NamedEncoding
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowContextSubstitution

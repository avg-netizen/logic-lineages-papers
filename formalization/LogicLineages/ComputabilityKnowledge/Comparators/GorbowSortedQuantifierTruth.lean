module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruth

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedQuantifierTruth
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedRevision GorbowFreeSupport GorbowNamedBinding
open GorbowFormulaComposition GorbowStandardInstances
open LogicLineages.ComputabilityKnowledge.GorbowSortedQuantifierTruth

def GuardDomains : Prop := ∀ n (t : Term n) P ρ,
  ((variableGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
    ∃ i,t.realize (interpretation GorbowSortedRegistry.ground P) ρ=variableNumber i) ∧
  ((fullTermGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
    ∃ s : Term 0,t.realize (interpretation GorbowSortedRegistry.ground P) ρ=termCode s) ∧
  ((arithmeticTermGuard t).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
    ∃ s : Term 0,t.realize (interpretation GorbowSortedRegistry.ground P) ρ=termCode s ∧ ArithmeticTerm s)

def NamedDomain : Prop := ∀ k (v f : Term k) P ρ,
  (namedGuard v f).realize (interpretation GorbowSortedRegistry.ground P) ρ ↔
    ∃ (n : Nat) (φ : Formula n) (i : Fin n),
      v.realize (interpretation GorbowSortedRegistry.ground P) ρ=variableNumber i.val ∧
      f.realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode φ ∧ formulaSupport φ={i.val}

def BindingFunctions : Prop := ∀ n (φ : Formula n) (i : Fin n), formulaSupport φ={i.val} →
  ∀ k (v f : Term k) P ρ,
    v.realize (interpretation GorbowSortedRegistry.ground P) ρ=variableNumber i.val →
    f.realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode φ →
    (allCodeTerm v f).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (bindAll i φ) ∧
    (exCodeTerm v f).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (bindEx i φ)

def InstanceFunction : Prop := ∀ n (φ : Formula n) (i : Fin n), formulaSupport φ={i.val} →
  ∀ (s : Term 0) k (v f t : Term k) P ρ,
    v.realize (interpretation GorbowSortedRegistry.ground P) ρ=variableNumber i.val →
    f.realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode φ →
    t.realize (interpretation GorbowSortedRegistry.ground P) ρ=termCode s →
    (instanceCodeTerm v f t).realize (interpretation GorbowSortedRegistry.ground P) ρ=formulaCode (namedClosedInstance i φ s)

def PositiveAxioms : Prop := ∀ initial k,
  forallAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0 ∧
  existsAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0 ∧
  barcanAxiom.realize (stage GorbowSortedRegistry.ground initial (k+1)) Fin.elim0

def Target : Prop := GuardDomains ∧ NamedDomain ∧ BindingFunctions ∧ InstanceFunction ∧ PositiveAxioms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedQuantifierTruth

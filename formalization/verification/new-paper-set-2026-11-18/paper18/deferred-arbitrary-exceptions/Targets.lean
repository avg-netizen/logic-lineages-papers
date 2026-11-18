module
public import LogicLineages.StandardControlCurrent.GraphDomains.Definitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphDomains.Targets
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion

def LiteralEnumeration : Prop := ∀ d gs rs p,
  Code.package d (sourceCode gs rs p) = (matrices d gs rs p).map Formula.encode

def Programs : Prop :=
  Computable (fun a : Nat × Nat => Code.package a.1 a.2) ∧
  Computable (fun a : Nat × Nat × Nat => Code.decide a.1 a.2.1 a.2.2)

def CaseTruth : Prop := ∀ d gs rs p ν,
  SourceHolds d gs rs p ν ↔ ∃ q ∈ matrices d gs rs p, Formula.eval ν q

def GuardedDomains : Prop := ∀ D d gs rs p,
  (∀ g ∈ gs, g.Valid D) → (∀ r ∈ rs, LinearRow r) → LinearFormula p →
  ∀ q ∈ matrices d gs rs p,
    Formula.allowed D q ∧ ∀ ν, Formula.eval ν q → Formula.meaningful q ν

def ActualHeadSpecialization : Prop := ∀ code, ValidHead code → ∀ input output,
  (actualHead code input output).Valid (headDegree code) ∧
  (actualHead code input output).Functional (headValue code)

/-- Stronger finite-presentation decision theorem: total functionality is not
needed for decidability. In source use, each graph is certified functional by
its actual graph theorem; word domains are certified separately. -/
def FiniteGraphDecision : Prop := ∀ D d gs rs p,
  (∀ g ∈ gs, g.Valid D) → (∀ r ∈ rs, LinearRow r) → LinearFormula p →
  (Code.decide D d (sourceCode gs rs p) = true ↔ ∃ ν, SourceHolds d gs rs p ν)

/-- Complete generic current18 m:lem:graph-domains, including literal encoded
positive-case enumeration, genuine programs, common-valuation semantics and
actual graph-theorem specialization. No free-parameter QE. -/
def FullGraphDomains : Prop := LiteralEnumeration ∧ Programs ∧ CaseTruth ∧
  GuardedDomains ∧ ActualHeadSpecialization ∧ FiniteGraphDecision

end LogicLineages.StandardControlCurrent.GraphDomains.Targets

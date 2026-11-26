module
public import LogicLineages.StandardControlCurrent.OrderedGuardsDefinitions
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.RankedRow
open OrdinalComparison PolynomialGraphCompletion RankedWordDecisionCompletion WordLinearDecisionCompletion
noncomputable def RowValue (r : Row) (ν : Nat → Nat) : Int :=
  r.1 + (r.2.map (fun a => a.1 * (OrderedGuards.wordValue a.2.2 (ν a.2.1) : Int))).sum
noncomputable def RowDomain (r : Row) (ν : Nat → Nat) : Prop :=
  ∀ a ∈ r.2, OrderedGuards.WordDomain a.2.2 (ν a.2.1)
noncomputable def OutcomeCorrect (maximum : Nat) (source : Row)
    (o : Outcome) (ν : Nat → Nat) : Prop :=
  (o.tag = 0 ∧ RowValue source ν < 0) ∨
  (o.tag = 2 ∧ 0 < RowValue source ν) ∨
  (o.tag = 3 ∧ LinearRow maximum o.row ∧ RowValue o.row ν = RowValue source ν)

/-- Syntax and semantics are both checked against the original finite row
family. Output guards retain all names, domains and correlations. -/
noncomputable def PackageCorrect (D maximum : Nat) (rows : List Row)
    (p : Package) : Prop :=
  (∀ c ∈ p.cases,
    Formula.allowed D c.guard ∧ linear maximum c.guard = true ∧
    FormulaNamesFrom (OriginalNames rows) c.guard ∧
    c.outcomes.length = rows.length ∧
    ∀ o ∈ c.outcomes, RowAllowed D o.row ∧ NamesFrom (OriginalNames rows) o.row ∧
      (o.tag = 0 ∨ o.tag = 2 ∨ (o.tag = 3 ∧ LinearRow maximum o.row))) ∧
  ∀ ν, Region p.tail maximum (OriginalNames rows) ν →
    (∀ r ∈ rows, RowDomain r ν) ∧
    (∀ c ∈ p.cases, Formula.meaningful c.guard ν ∧
      ∀ o ∈ c.outcomes, RowDomain o.row ν) ∧
    (∃ c ∈ p.cases, Formula.eval ν c.guard) ∧
    ∀ c ∈ p.cases, Formula.eval ν c.guard →
      List.Forall₂ (fun r o => OutcomeCorrect maximum r o ν) rows c.outcomes

end LogicLineages.StandardControlCurrent.RankedRow

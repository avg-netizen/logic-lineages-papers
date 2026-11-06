module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadDerivedProof

public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDomainsProof
open ExpressionNodeProof

theorem rows_domains_and_degree (hHead : Targets.HeadEquationExact) (t : Expr) :
    ValidExpr t → ∀ D : Nat,
    (∀ code ∈ t.heads, UnaryAllowed D (headRow code)) →
    ∀ (start : Nat) (row : Row), row ∈ rows start t →
      RowAllowed D row ∧ ∀ ν : Nat → Nat, RowDomain row ν := by
  induction t with
  | numeral n =>
      intro ht D hdegrees start row hr
      have hrow : row = numeralRow start n := List.mem_singleton.mp hr
      subst row
      exact ⟨numeral_allowed D start n,numeral_domain start n⟩
  | «variable» i =>
      intro ht D hdegrees start row hr
      have hrow : row = variableRow start i := List.mem_singleton.mp hr
      subst row
      exact ⟨variable_allowed D start i,variable_domain start i⟩
  | add a b iha ihb =>
      intro ht D hdegrees start row hr
      have hvalid := valid_add ht
      simp only [rows,List.mem_append,List.mem_singleton] at hr
      rcases hr with (hr | hr) | rfl
      · exact iha hvalid.1 D (fun code hc => hdegrees code (List.mem_append_left _ hc))
          start row hr
      · exact ihb hvalid.2 D (fun code hc => hdegrees code (List.mem_append_right _ hc))
          (start+nodeCount a) row hr
      · exact ⟨addition_allowed D _ _ _,addition_domain _ _ _⟩
  | scale k a ih =>
      intro ht D hdegrees start row hr
      simp only [rows,List.mem_append,List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ih (valid_scale ht) D hdegrees start row hr
      · exact ⟨scale_allowed D _ _ _,scale_domain _ _ _⟩
  | collapse code a ih =>
      intro ht D hdegrees start row hr
      have hvalid := valid_collapse ht
      simp only [rows,List.mem_append,List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ih hvalid.1 D (fun q hq => hdegrees q (List.mem_append_left _ hq)) start row hr
      · refine ⟨HeadDerivedProof.headEquation_allowed
          (hdegrees code (List.mem_append_right _ (List.mem_singleton_self _))),?_⟩
        intro ν
        exact ((hHead code hvalid.2 (output start a) (output start (.collapse code a))).2 ν).1

theorem expressionDomainsAndDegree (hGraphs : Targets.HeadGraphExact) :
    ExpressionTargets.ExpressionDomainsAndDegree := by
  intro t ht
  have hfamily := HeadDerivedProof.finiteFamilyDegree hGraphs t.heads ht
  have hrows := rows_domains_and_degree (HeadDerivedProof.headEquationExact hGraphs)
    t ht (exprDegree t) hfamily.2
  refine ⟨hfamily.1,hrows,?_⟩
  intro resultName row hr
  change row ∈ rows (freshStart t resultName) t ++
    [variableRow resultName (output (freshStart t resultName) t)] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hrows (freshStart t resultName) row hr
  · have hrow := List.mem_singleton.mp hr
    subst row
    exact ⟨variable_allowed (exprDegree t) _ _,variable_domain _ _⟩

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDomainsProof

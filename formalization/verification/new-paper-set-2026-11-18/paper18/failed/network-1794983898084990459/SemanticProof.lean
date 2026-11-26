module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Targets
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.DomainsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadDerivedProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDomainsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadStatementChecks

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.SemanticProof
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion
open PolynomialBoolean.SemanticBasics PolynomialBoolean.DomainsProof ExpressionNodeProof

 theorem valid_heads (hs : List HeadClause) (bs : List Block) (rs : List Row) (p : Formula)
    (hv : Valid hs bs rs p) : ∀ c ∈ heads hs bs, ValidHead c := by
  intro c hc
  rcases List.mem_append.mp hc with hh | hb
  · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hh
    exact hv.1 h hh
  · obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hb
    exact hv.2.1 b hb c hc

 theorem linear_good (D : Nat) (r : Row) (h : LinearRow r) :
    RowAllowed D r ∧ ∀ ν, RowDomain r ν := by
  constructor
  · intro a ha
    rw [h a ha]
    trivial
  · intro ν a ha
    rw [h a ha]
    trivial

 theorem row_good (hs : List HeadClause) (bs : List Block) (rs : List Row) (p : Formula)
    (hv : Valid hs bs rs p) :
    ∀ r ∈ allRows hs bs rs, RowAllowed (degree hs bs) r ∧ ∀ ν, RowDomain r ν := by
  have hf := HeadStatementChecks.finite_family_degree (heads hs bs) (valid_heads hs bs rs p hv)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hr
      refine ⟨HeadDerivedProof.headEquation_allowed (hf.2 h.1 ?_),?_⟩
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨h,hh,rfl⟩)
      · intro ν
        exact ((HeadStatementChecks.head_equation_exact h.1 (hv.1 h hh) h.2.1 h.2.2).2 ν).1
    · obtain ⟨b,hb,hr⟩ := List.mem_flatMap.mp hr
      rcases List.mem_append.mp hr with hr | hr
      · apply ExpressionDomainsProof.rows_domains_and_degree HeadStatementChecks.head_equation_exact
          b.term (hv.2.1 b hb) (degree hs bs) _ b.start r hr
        intro c hc
        exact hf.2 c (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hb,hc⟩))
      · have he := List.mem_singleton.mp hr
        subst r
        exact ⟨variable_allowed _ _ _,variable_domain _ _⟩
  · exact linear_good _ r (hv.2.2.1 r hr)

 theorem output_good (D : Nat) (p : Formula) (h : LinearFormula p) : Good D p := by
  constructor
  · intro a ha
    rw [h a ha]
    trivial
  · intro ν a ha
    rw [h a ha]
    trivial

 theorem all_values (hs : List HeadClause) (bs : List Block) (rs : List Row) (p : Formula)
    (hv : Valid hs bs rs p) (ν : Nat → Nat) :
    (∀ r ∈ allRows hs bs rs, RowValue r ν = 0) ↔
      (∀ h ∈ hs, ν h.2.2 = headValue h.1 (ν h.2.1)) ∧
      (∀ b ∈ bs, RowsHold b.rows ν) ∧ (∀ r ∈ rs, RowValue r ν = 0) := by
  have domains := row_good hs bs rs p hv
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro a ha
      apply ((HeadStatementChecks.head_equation_exact a.1 (hv.1 a ha) a.2.1 a.2.2).2 ν).2.mp
      apply h
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩))
    · intro b hb r hr
      have hm : r ∈ allRows hs bs rs := List.mem_append_left _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hb,hr⟩))
      exact ⟨(domains r hm).2 ν,h r hm⟩
    · intro r hr
      exact h r (List.mem_append_right _ hr)
  · rintro ⟨hh,hb,hr⟩ r hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
        exact ((HeadStatementChecks.head_equation_exact a.1 (hv.1 a ha) a.2.1 a.2.2).2 ν).2.mpr (hh a ha)
      · obtain ⟨b,hb',hm⟩ := List.mem_flatMap.mp hm
        exact (hb b hb' r hm).2
    · exact hr r hm

 theorem full : Targets.DomainsAndSemantics := by
  intro d hs bs rs p hv
  have hf := HeadStatementChecks.finite_family_degree (heads hs bs) (valid_heads hs bs rs p hv)
  have hg := good_conj (positive_good (degree hs bs) d)
    (good_conj (good_graph (degree hs bs) (allRows hs bs rs) (row_good hs bs rs p hv))
      (output_good (degree hs bs) p hv.2.2.2))
  refine ⟨hf.1,hg.1,hg.2,?_⟩
  intro ν
  simp only [matrix,Formula.eval,positive_eval,graph_eval,all_values hs bs rs p hv ν,SourceHolds]
  constructor
  · rintro ⟨hp,⟨hh,hb,hr⟩,ho⟩
    exact ⟨hp,hh,hb,hr,ho⟩
  · rintro ⟨hp,hh,hb,hr,ho⟩
    exact ⟨hp,⟨hh,hb,hr⟩,ho⟩
end LogicLineages.StandardControlCurrent.GraphNetwork.SemanticProof

module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.SemanticBasics
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDomainsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadStatementChecks

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.DomainsProof
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion
open LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit

def Good (D : Nat) (p : Formula) : Prop := Formula.allowed D p ∧ ∀ ν, Formula.meaningful p ν

theorem good_top (D : Nat) : Good D .top := by
  simp [Good,Formula.allowed,Formula.meaningful,Formula.tokens,Boolean.atoms]
theorem good_bot (D : Nat) : Good D .bot := by
  simp [Good,Formula.allowed,Formula.meaningful,Formula.tokens,Boolean.atoms]
theorem good_neg {D : Nat} {p : Formula} (h : Good D p) : Good D (.neg p) := h

theorem good_conj {D : Nat} {p q : Formula} (hp : Good D p) (hq : Good D q) : Good D (.conj p q) := by
  constructor
  · intro t ht
    simp only [Formula.tokens,Boolean.atoms,List.flatMap_append,List.mem_append] at ht
    exact ht.elim (hp.1 t) (hq.1 t)
  · intro ν t ht
    simp only [Formula.tokens,Boolean.atoms,List.flatMap_append,List.mem_append] at ht
    exact ht.elim (hp.2 ν t) (hq.2 ν t)

theorem good_disj {D : Nat} {p q : Formula} (hp : Good D p) (hq : Good D q) : Good D (.disj p q) :=
  good_conj hp hq

theorem good_atom (D : Nat) (r : Row) (ha : RowAllowed D r) (hd : ∀ ν, RowDomain r ν) :
    Good D (.atom (.nonnegative r)) := by
  constructor
  · intro t ht
    change t ∈ r.2.map Prod.snd at ht
    obtain ⟨a,ha',rfl⟩ := List.mem_map.mp ht
    exact ha a ha'
  · intro ν t ht
    change t ∈ r.2.map Prod.snd at ht
    obtain ⟨a,ha',rfl⟩ := List.mem_map.mp ht
    exact hd ν a ha'

theorem good_equality (D : Nat) (r : Row) (ha : RowAllowed D r) (hd : ∀ ν, RowDomain r ν) :
    Good D (equality r) := by
  apply good_conj (good_atom D r ha hd)
  apply good_atom
  · intro a hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    exact ha b hb
  · intro ν a hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    exact hd ν b hb

theorem relation_allowed (D : Nat) (s : Bool) (a b : Nat) : RowAllowed D (relationRow s a b) := by
  intro v hv
  simp only [relationRow,List.mem_cons,List.mem_singleton] at hv
  rcases hv with rfl | rfl <;> simp [WordAllowed]
theorem relation_domain (s : Bool) (a b : Nat) (ν : Nat → Nat) : RowDomain (relationRow s a b) ν := by
  intro v hv
  simp only [relationRow,List.mem_cons,List.mem_singleton] at hv
  rcases hv with rfl | rfl <;> trivial

theorem good_output (D : Nat) (r : Relation) (a b : Nat) : Good D (outputTest r a b) := by
  cases r
  · exact good_equality D _ (relation_allowed D false a b) (relation_domain false a b)
  · exact good_atom D _ (relation_allowed D false a b) (relation_domain false a b)
  · exact good_atom D _ (relation_allowed D true a b) (relation_domain true a b)

theorem output_good (D start : Nat) (p : Source) : Good D (compile start p).2.2 := by
  induction p generalizing start with
  | truth b => cases b; exact good_bot D; exact good_top D
  | atom r a b => exact good_output D r _ _
  | neg p ih => exact good_neg (ih start)
  | conj p q ihp ihq => exact good_conj (ihp start) (ihq (compile start p).1)
  | disj p q ihp ihq => exact good_disj (ihp start) (ihq (compile start p).1)

theorem positive_good (D d : Nat) : Good D (positiveFormula d) := by
  have aux : ∀ is : List Nat, Good D
      (is.foldr (fun i q => .conj (.atom (.nonnegative (-1,[(1,i,[])]))) q) .top) := by
    intro is
    induction is with
    | nil => exact good_top D
    | cons i is ih =>
      apply good_conj _ ih
      apply good_atom
      · intro a ha
        have := List.mem_singleton.mp ha
        subst a
        simp [WordAllowed]
      · intro ν a ha
        have := List.mem_singleton.mp ha
        subst a
        trivial
  exact aux (List.range d)

theorem valid_heads (d : Nat) (p : Source) (hv : p.Valid d) : ∀ c ∈ p.heads, ValidHead c := by
  induction p with
  | truth b => simp [Source.heads]
  | atom r a b =>
    intro c hc
    exact (List.mem_append.mp hc).elim (hv.1 c) (hv.2.1 c)
  | neg p ih => exact ih hv
  | conj p q ihp ihq | disj p q ihp ihq =>
    intro c hc
    exact (List.mem_append.mp hc).elim (ihp hv.1 c) (ihq hv.2 c)

theorem compiled_rows (d D start : Nat) (p : Source) (hv : p.Valid d)
    (heads : ∀ c ∈ p.heads, UnaryAllowed D (headRow c)) :
    ∀ r ∈ (compile start p).2.1, RowAllowed D r ∧ ∀ ν, RowDomain r ν := by
  induction p generalizing start with
  | truth b => simp [compile]
  | atom rel a b =>
    intro r hr
    rcases List.mem_append.mp hr with ha | hb
    · exact ExpressionDomainsProof.rows_domains_and_degree HeadStatementChecks.head_equation_exact
        a hv.1 D (fun c hc => heads c (List.mem_append_left _ hc)) start r ha
    · exact ExpressionDomainsProof.rows_domains_and_degree HeadStatementChecks.head_equation_exact
        b hv.2.1 D (fun c hc => heads c (List.mem_append_right _ hc)) _ r hb
  | neg p ih => exact ih hv heads start
  | conj p q ihp ihq | disj p q ihp ihq =>
    intro r hr
    rcases List.mem_append.mp hr with hp | hq
    · exact ihp hv.1 (fun c hc => heads c (List.mem_append_left _ hc)) start r hp
    · exact ihq hv.2 (fun c hc => heads c (List.mem_append_right _ hc)) (compile start p).1 r hq

theorem good_graph (D : Nat) (rs : List Row)
    (h : ∀ r ∈ rs, RowAllowed D r ∧ ∀ ν, RowDomain r ν) : Good D (graphFormula rs) := by
  induction rs with
  | nil => exact good_top D
  | cons r rs ih =>
    exact good_conj (good_equality D r (h r List.mem_cons_self).1 (h r List.mem_cons_self).2)
      (ih (fun s hs => h s (List.mem_cons_of_mem r hs)))

theorem full : Targets.MatrixDomains := by
  intro d p hv
  have hfamily := HeadStatementChecks.finite_family_degree p.heads (valid_heads d p hv)
  refine ⟨hfamily.1,?_⟩
  intro c
  have hg := good_graph p.degree (compile d p).2.1 (compiled_rows d p.degree d p hv hfamily.2)
  apply good_conj (positive_good p.degree d)
  apply good_conj hg
  cases c
  · exact output_good p.degree d p
  · exact good_neg (output_good p.degree d p)

end LogicLineages.StandardControlCurrent.PolynomialBoolean.DomainsProof

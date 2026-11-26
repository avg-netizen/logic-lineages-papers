module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportBodyProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
open PolynomialGraphCompletion WordLinearDecisionCompletion OutcomeTransport
open LogicLineages.ModelsAlgebra.Forests

def rowTokens (r : Row) : List Token := r.2.map Prod.snd

theorem transport_tokens_conj (p q : Formula) :
    Formula.tokens (.conj p q) = p.tokens++q.tokens := by
  simp only [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]

theorem transport_tokens_disj (p q : Formula) :
    Formula.tokens (.disj p q) = p.tokens++q.tokens := by
  simp only [Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]

theorem congruence_atom_member (p : Formula) (a : Nat × Row) (ha : a ∈ congruences p) :
    Atom.divisible a.1 a.2 ∈ p.atoms := by
  obtain ⟨b,hb,he⟩ := List.mem_filterMap.mp ha
  cases b with
  | nonnegative r => simp at he
  | divisible m r =>
      have he' : (m,r) = a := by simpa only [Option.some.injEq] using he
      cases he'
      exact hb

theorem original_congruence_token (p : Formula) (a : Nat × Row)
    (ha : a ∈ congruences p) (t : Token) (ht : t ∈ rowTokens a.2) : t ∈ p.tokens := by
  exact List.mem_flatMap.mpr ⟨.divisible a.1 a.2,congruence_atom_member p a ha,ht⟩

theorem rowAllowed_tokens (D : Nat) (r : Row) (h : RowAllowed D r) :
    ∀ t ∈ rowTokens r, WordAllowed D t.2 := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  exact h a ha

theorem rowDomain_tokens (r : Row) (ν : Nat → Nat) (h : RowDomain r ν) :
    ∀ t ∈ rowTokens r, WordDomain t.2 (ν t.1) := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  exact h a ha

theorem rowNames_tokens (names : List Nat) (r : Row) (h : NamesFrom names r) :
    ∀ t ∈ rowTokens r, t.1 ∈ names := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  exact h a.2.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)

theorem rowLinear_tokens (maximum : Nat) (r : Row) (h : LinearRow maximum r) :
    ∀ t ∈ rowTokens r, (t.1 != maximum || t.2.isEmpty) = true := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
  by_cases hn : a.2.1 = maximum
  · have hw := h a ha hn
    simp [hn,hw]
  · simp [hn]

theorem outcomeFormula_tokens_subset (d : OutcomeData) (t : Token)
    (ht : t ∈ Formula.tokens (outcomeFormula d)) : t ∈ rowTokens d.2 := by
  by_cases h0 : d.1 = 0
  · simp [outcomeFormula,h0,Formula.tokens,CotreePresburgerUnit.Boolean.atoms] at ht
  · by_cases h2 : d.1 = 2
    · simp [outcomeFormula,h0,h2,Formula.tokens,CotreePresburgerUnit.Boolean.atoms] at ht
    · simpa [outcomeFormula,h0,h2,Formula.tokens,CotreePresburgerUnit.Boolean.atoms,
        Atom.row,rowTokens] using ht

theorem lookup_property (Q : OutcomeData → Prop) (key : Nat) (table : Table) :
    Q (0,(0,[])) → (∀ entry ∈ table, Q entry.2) → Q (lookup key table) := by
  induction table with
  | nil => intro hdefault htable; exact hdefault
  | cons entry rest ih =>
      rcases entry with ⟨k,o⟩
      intro hdefault htable
      by_cases hk : k = key
      · simpa only [lookup,if_pos hk] using htable (k,o) (by simp)
      · simpa only [lookup,if_neg hk] using
          ih hdefault (fun entry he => htable entry (by simp [he]))

theorem makeTable_property (Q : OutcomeData → Prop) (rows : List Row) (outcomes : List Outcome)
    (h : ∀ o ∈ outcomes, Q (outcomeData o)) :
    ∀ entry ∈ makeTable rows (outcomes.map outcomeData), Q entry.2 := by
  intro entry he
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hout := (List.of_mem_zip hp).2
  obtain ⟨o,ho,heq⟩ := List.mem_map.mp hout
  simpa only [heq] using h o ho

theorem lookup_tokens_property (P : Token → Prop) (rows : List Row) (outcomes : List Outcome)
    (key : Nat) (h : ∀ o ∈ outcomes, ∀ t ∈ Formula.tokens (outcomeFormula (outcomeData o)), P t) :
    ∀ t ∈ Formula.tokens (outcomeFormula
      (lookup key (makeTable rows (outcomes.map outcomeData)))), P t := by
  apply lookup_property (fun d => ∀ t ∈ Formula.tokens (outcomeFormula d), P t)
    key (makeTable rows (outcomes.map outcomeData))
  · simp [outcomeFormula,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
  · exact makeTable_property (fun d => ∀ t ∈ Formula.tokens (outcomeFormula d), P t) rows outcomes h

/-- Literal tokens of the rewritten body come only from unchanged source
congruences and the selected actual outcome renderings. This is independent
of Boolean truth, polarity and branch consistency. -/
theorem rewriteWith_all_tokens (table : Table) (P : Token → Prop) : ∀ p : Formula,
    (∀ a ∈ congruences p, ∀ t ∈ rowTokens a.2, P t) →
    (∀ r ∈ inequalityRows p, ∀ t ∈ Formula.tokens
      (outcomeFormula (lookup (Encodable.encode r) table)), P t) →
    ∀ t ∈ Formula.tokens (rewriteWith table p), P t := by
  intro p
  induction p with
  | bot => intro hc hi t ht; simp [rewriteWith,Formula.tokens,CotreePresburgerUnit.Boolean.atoms] at ht
  | top => intro hc hi t ht; simp [rewriteWith,Formula.tokens,CotreePresburgerUnit.Boolean.atoms] at ht
  | atom a =>
      intro hc hi t ht
      cases a with
      | nonnegative r =>
          exact hi r (by simp [inequalityRows,CotreePresburgerUnit.Boolean.atoms]) t ht
      | divisible m r =>
          apply hc (m,r) (by simp [congruences,CotreePresburgerUnit.Boolean.atoms]) t
          simpa [rewriteWith,Formula.tokens,CotreePresburgerUnit.Boolean.atoms,Atom.row,rowTokens] using ht
  | neg p ih => intro hc hi t ht; exact ih hc hi t ht
  | conj p q ihp ihq =>
      intro hc hi t ht
      have hm : t ∈ Formula.tokens (rewriteWith table p) ∨ t ∈ Formula.tokens (rewriteWith table q) := by
        simpa only [rewriteWith,transport_tokens_conj,List.mem_append] using ht
      rcases hm with hm | hm
      · apply ihp ?_ ?_ t hm
        · intro a ha
          exact hc a (by rw [congruences_conj]; exact List.mem_append_left _ ha)
        · intro r hr
          exact hi r (by rw [inequalityRows_conj]; exact List.mem_append_left _ hr)
      · apply ihq ?_ ?_ t hm
        · intro a ha
          exact hc a (by rw [congruences_conj]; exact List.mem_append_right _ ha)
        · intro r hr
          exact hi r (by rw [inequalityRows_conj]; exact List.mem_append_right _ hr)
  | disj p q ihp ihq =>
      intro hc hi t ht
      have hm : t ∈ Formula.tokens (rewriteWith table p) ∨ t ∈ Formula.tokens (rewriteWith table q) := by
        simpa only [rewriteWith,transport_tokens_disj,List.mem_append] using ht
      rcases hm with hm | hm
      · apply ihp ?_ ?_ t hm
        · intro a ha
          exact hc a (by rw [congruences_disj]; exact List.mem_append_left _ ha)
        · intro r hr
          exact hi r (by rw [inequalityRows_disj]; exact List.mem_append_left _ hr)
      · apply ihq ?_ ?_ t hm
        · intro a ha
          exact hc a (by rw [congruences_disj]; exact List.mem_append_right _ ha)
        · intro r hr
          exact hi r (by rw [inequalityRows_disj]; exact List.mem_append_right _ hr)

private theorem rewrite_tokens_property (P : Token → Prop) (p : Formula) (outcomes : List Outcome)
    (hc : ∀ a ∈ congruences p, ∀ t ∈ rowTokens a.2, P t)
    (ho : ∀ o ∈ outcomes, ∀ t ∈ Formula.tokens (outcomeFormula (outcomeData o)), P t) :
    ∀ t ∈ Formula.tokens (OutcomeTransport.rewrite p outcomes), P t := by
  apply rewriteWith_all_tokens _ P p hc
  intro r hr
  exact lookup_tokens_property P (inequalityRows p) outcomes (Encodable.encode r) ho

theorem bodySyntaxAndDomains : OutcomeTransportTargets.BodySyntaxAndDomains := by
  intro D maximum p outcomes hp hcong hlength hout
  have hallowed : Formula.allowed D (OutcomeTransport.rewrite p outcomes) := by
    apply rewrite_tokens_property (fun t => WordAllowed D t.2) p outcomes
    · intro a ha t ht
      exact hp t (original_congruence_token p a ha t ht)
    · intro o ho t ht
      exact rowAllowed_tokens D o.row (hout o ho).1 t (outcomeFormula_tokens_subset _ t ht)
  have hlinear : linear maximum (OutcomeTransport.rewrite p outcomes) = true := by
    apply List.all_eq_true.mpr
    apply rewrite_tokens_property (fun t => (t.1 != maximum || t.2.isEmpty) = true) p outcomes
    · intro a ha
      exact rowLinear_tokens maximum a.2 (hcong a ha)
    · intro o ho
      rcases (hout o ho).2.2 with h0 | h2 | ⟨h3,hlin⟩
      · simp [outcomeFormula,outcomeData,h0,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
      · simp [outcomeFormula,outcomeData,h2,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
      · intro t ht
        exact rowLinear_tokens maximum o.row hlin t (outcomeFormula_tokens_subset _ t ht)
  have hnames : FormulaNamesFrom p.variables (OutcomeTransport.rewrite p outcomes) := by
    have htokens : ∀ t ∈ Formula.tokens (OutcomeTransport.rewrite p outcomes), t.1 ∈ p.variables := by
      apply rewrite_tokens_property (fun t => t.1 ∈ p.variables) p outcomes
      · intro a ha t ht
        exact List.mem_map.mpr ⟨t,original_congruence_token p a ha t ht,rfl⟩
      · intro o ho t ht
        exact rowNames_tokens p.variables o.row (hout o ho).2.1 t (outcomeFormula_tokens_subset _ t ht)
    intro i hi
    obtain ⟨t,ht,he⟩ := List.mem_map.mp hi
    simpa only [he] using htokens t ht
  refine ⟨hallowed,hlinear,hnames,?_⟩
  intro ν hsource hdomains
  apply rewrite_tokens_property (fun t => WordDomain t.2 (ν t.1)) p outcomes
  · intro a ha t ht
    exact hsource t (original_congruence_token p a ha t ht)
  · intro o ho t ht
    exact rowDomain_tokens o.row ν (hdomains o ho) t (outcomeFormula_tokens_subset _ t ht)

/- Explicit per-file audit includes private helpers before module export. -/
#print axioms transport_tokens_conj
#print axioms transport_tokens_disj
#print axioms congruence_atom_member
#print axioms original_congruence_token
#print axioms rowAllowed_tokens
#print axioms rowDomain_tokens
#print axioms rowNames_tokens
#print axioms rowLinear_tokens
#print axioms outcomeFormula_tokens_subset
#print axioms lookup_property
#print axioms makeTable_property
#print axioms lookup_tokens_property
#print axioms rewriteWith_all_tokens
#print axioms rewrite_tokens_property
#print axioms bodySyntaxAndDomains

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof

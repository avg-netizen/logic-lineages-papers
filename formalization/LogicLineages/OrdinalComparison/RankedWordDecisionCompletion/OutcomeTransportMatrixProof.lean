module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportSyntaxProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerSingleProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof
open PolynomialGraphCompletion WordLinearDecisionCompletion OutcomeTransport
open LogicLineages.ModelsAlgebra.Forests

theorem source_atom_row_allowed (D : Nat) (p : Formula) (a : Atom)
    (hp : Formula.allowed D p) (ha : a ∈ p.atoms) : RowAllowed D a.row := by
  intro b hb
  exact hp b.2 (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)

theorem source_atom_row_names (p : Formula) (a : Atom) (ha : a ∈ p.atoms) :
    NamesFrom p.variables a.row := by
  intro i hi
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hi
  exact List.mem_map.mpr ⟨b.2,List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩,rfl⟩

theorem inequality_atom_member (p : Formula) (r : Row) (hr : r ∈ inequalityRows p) :
    Atom.nonnegative r ∈ p.atoms := by
  obtain ⟨a,ha,he⟩ := List.mem_filterMap.mp hr
  cases a with
  | nonnegative s =>
      have he' : s = r := by simpa only [Option.some.injEq] using he
      subst r
      exact ha
  | divisible m s => simp at he

theorem inequality_names_from (p : Formula) :
    ∀ i ∈ OriginalNames (inequalityRows p), i ∈ p.variables := by
  intro i hi
  obtain ⟨r,hr,hi⟩ := List.mem_flatMap.mp hi
  exact source_atom_row_names p (.nonnegative r) (inequality_atom_member p r hr) i hi

/-- The cutoff pays every original atom, not merely rows whose sign survives
in an active Boolean branch. Zero coefficient occurrences also remain here. -/
theorem originalTail_meaningful (D : Nat) (p : Formula) (ν : Nat → Nat)
    (hp : Formula.allowed D p) (hν : ∀ i ∈ p.variables, originalTail p ≤ ν i) :
    Formula.meaningful p ν := by
  intro t ht
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
  have hbound : Algorithm.rowTail a.row ≤ originalTail p :=
    AlgorithmProof.member_le_foldMax _ _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hrow := AlgorithmProof.rowTail_domain D a.row ν
    (source_atom_row_allowed D p a hp ha) (fun i hi =>
      hbound.trans (hν i (source_atom_row_names p a ha i hi)))
  exact hrow b hb

theorem transport_allowed_conj (D : Nat) (p q : Formula)
    (hp : Formula.allowed D p) (hq : Formula.allowed D q) :
    Formula.allowed D (.conj p q) := by
  intro t ht
  rw [transport_tokens_conj] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

theorem transport_linear_conj (maximum : Nat) (p q : Formula)
    (hp : linear maximum p = true) (hq : linear maximum q = true) :
    linear maximum (.conj p q) = true := by
  simp only [linear,transport_tokens_conj,List.all_append,Bool.and_eq_true]
  exact ⟨hp,hq⟩

theorem transport_names_conj (names : List Nat) (p q : Formula)
    (hp : FormulaNamesFrom names p) (hq : FormulaNamesFrom names q) :
    FormulaNamesFrom names (.conj p q) := by
  intro i hi
  have hm : i ∈ p.variables ∨ i ∈ q.variables := by
    simpa only [Formula.variables,transport_tokens_conj,List.map_append,List.mem_append] using hi
  rcases hm with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem transport_meaningful_conj (p q : Formula) (ν : Nat → Nat)
    (hp : Formula.meaningful p ν) (hq : Formula.meaningful q ν) :
    Formula.meaningful (.conj p q) ν := by
  intro t ht
  rw [transport_tokens_conj] at ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

/-- Generic package transport is a local lemma only. The frozen actual target
below discharges its package premise with the accepted concrete row runner. -/
theorem transform_correct (D maximum : Nat) (p : Formula) (pack : Package)
    (hp : Formula.allowed D p) (hcong : CongruencesLinear maximum p)
    (hpack : PackageCorrect D maximum (inequalityRows p) pack) :
    MatrixCorrect D maximum p (transform p pack) := by
  have hnames := inequality_names_from p
  have hbody : ∀ c ∈ pack.cases,
      Formula.allowed D (OutcomeTransport.rewrite p c.outcomes) ∧
      linear maximum (OutcomeTransport.rewrite p c.outcomes) = true ∧
      FormulaNamesFrom p.variables (OutcomeTransport.rewrite p c.outcomes) ∧
      ∀ ν, Formula.meaningful p ν → (∀ o ∈ c.outcomes, RowDomain o.row ν) →
        Formula.meaningful (OutcomeTransport.rewrite p c.outcomes) ν := by
    intro c hc
    rcases hpack.1 c hc with ⟨ha,hl,hn,hcount,hout⟩
    apply bodySyntaxAndDomains D maximum p c.outcomes hp hcong hcount
    intro o ho
    have h := hout o ho
    exact ⟨h.1,fun i hi => hnames i (h.2.1 i hi),h.2.2⟩
  constructor
  · intro q hq
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
    rcases hpack.1 c hc with ⟨ha,hl,hn,hcount,hout⟩
    have hb := hbody c hc
    exact ⟨transport_allowed_conj D _ _ ha hb.1,
      transport_linear_conj maximum _ _ hl hb.2.1,
      transport_names_conj p.variables _ _ (fun i hi => hnames i (hn i hi)) hb.2.2.1⟩
  · intro ν hregion
    have hsource : Formula.meaningful p ν :=
      originalTail_meaningful D p ν hp (fun i hi =>
        (Nat.le_max_right _ _).trans (hregion i hi).1)
    have hrowRegion : Region pack.tail maximum (OriginalNames (inequalityRows p)) ν := by
      intro i hi
      have h := hregion i (hnames i hi)
      exact ⟨(Nat.le_max_left _ _).trans h.1,h.2⟩
    rcases hpack.2 ν hrowRegion with ⟨hrowDomains,hcaseDomains,hcover,hcorrect⟩
    refine ⟨hsource,?_,?_⟩
    · intro q hq
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
      exact transport_meaningful_conj _ _ ν (hcaseDomains c hc).1
        ((hbody c hc).2.2.2 ν hsource (hcaseDomains c hc).2)
    · constructor
      · intro htrue
        obtain ⟨c,hc,hguard⟩ := hcover
        refine ⟨.conj c.guard (OutcomeTransport.rewrite p c.outcomes),
          List.mem_map.mpr ⟨c,hc,rfl⟩,hguard,?_⟩
        exact (exactCorrelatedBody.1 maximum p c.outcomes ν (hcorrect c hc hguard)).mpr htrue
      · rintro ⟨q,hq,htrue⟩
        obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
        exact (exactCorrelatedBody.1 maximum p c.outcomes ν (hcorrect c hc htrue.1)).mp htrue.2

/-- No package-correctness or row-termination assumption is exposed: the
original concrete Runner.compile is selected internally at the same inputs. -/
theorem exactActualMatrix : OutcomeTransportTargets.ExactActualMatrix := by
  intro D maximum p hDegree hp hcong
  apply transform_correct D maximum p (Runner.compile D maximum (inequalityRows p)) hp hcong
  apply RunnerProof.exactFamilyPackage D maximum (inequalityRows p) hDegree
  intro r hr
  exact source_atom_row_allowed D p (.nonnegative r) hp (inequality_atom_member p r hr)

#print axioms source_atom_row_allowed
#print axioms source_atom_row_names
#print axioms inequality_atom_member
#print axioms inequality_names_from
#print axioms originalTail_meaningful
#print axioms transport_allowed_conj
#print axioms transport_linear_conj
#print axioms transport_names_conj
#print axioms transport_meaningful_conj
#print axioms transform_correct
#print axioms exactActualMatrix

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof

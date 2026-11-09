module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmClassSemanticProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPartitionProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmGreatestClassProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

theorem foldRows_names (names : List Nat) (rows : List Row)
    (h : ∀ r ∈ rows, NamesFrom names r) : NamesFrom names (rows.foldr rowAdd (0,[])) := by
  induction rows with
  | nil => simp [NamesFrom,rowVariables]
  | cons r rows ih =>
      intro i hi
      have hm : i ∈ rowVariables r ∨ i ∈ rowVariables (rows.foldr rowAdd (0,[])) := by
        simpa [rowVariables,rowAdd,List.map_append] using hi
      rcases hm with hi | hi
      · exact h r (by simp) i hi
      · exact ih (fun s hs => h s (by simp [hs])) i hi

theorem ordinaryResidual_names (a : Item) (i : Nat)
    (hi : i ∈ rowVariables (ordinaryResidual a)) : i = a.2.1 := by
  by_cases hc : isCounter a = true
  · simp only [ordinaryResidual,hc,if_true,rowVariables,List.map_map,Function.comp_def] at hi
    obtain ⟨p,hp,he⟩ := List.mem_map.mp hi
    exact he.symm
  · simp [ordinaryResidual,hc,rowVariables] at hi

theorem counterResidual_names (reference : Nat) (a : Item) (i : Nat)
    (hi : i ∈ rowVariables (counterResidual reference a)) : i = a.2.1 := by
  simp only [counterResidual,rowVariables,List.map_map,Function.comp_def] at hi
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hi
  exact he.symm

theorem classReplacement_syntax (D : Nat) (r : Row) (xs : List Item)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hxs : ∀ a ∈ xs, a ∈ active (canonicalRow r)) :
    RowAllowed D (classReplacement D xs) ∧ NamesFrom (rowVariables r) (classReplacement D xs) := by
  have hname : ∀ a ∈ xs, a.2.1 ∈ rowVariables r := by
    intro a ha
    exact canonical_names r a.2.1
      (List.mem_map.mpr ⟨a,(List.mem_filter.mp (hxs a ha)).1,rfl⟩)
  by_cases ho : hasOrdinary xs = true
  · simp only [classReplacement,ho,if_true]
    constructor
    · apply foldRows_allowed
      intro s hs
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      exact (ordinaryResidual_identity D r a hD (hxs a ha) (fun _ => sourceTail a) le_rfl).1
    · apply foldRows_names
      intro s hs i hi
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      rw [ordinaryResidual_names a i hi]
      exact hname a ha
  · have hf : hasOrdinary xs = false := Bool.eq_false_of_not_eq_true ho
    have hc := hasOrdinary_false xs hf
    have href : 3 ≤ leastRank D xs := leastRank_lower D 3 xs (by omega) (by
      intro a ha
      have hp := counter_parameters D r a hD (hxs a ha) (hc a ha)
      omega)
    simp only [classReplacement,hf,Bool.false_eq_true,if_false]
    constructor
    · apply foldRows_allowed
      intro s hs
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      exact (counterResidual_allowed_domain D r a hD (hxs a ha) (hc a ha)
        (leastRank D xs) href (leastRank_le_member D xs a ha)
        (fun _ => sourceTail a) le_rfl).1
    · apply foldRows_names
      intro s hs i hi
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      rw [counterResidual_names (leastRank D xs) a i hi]
      exact hname a ha

theorem outside_subset (r : Row) (labels : List Nat) (removed : Nat) :
    ∀ a ∈ outside r labels removed, a ∈ r.2 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact (List.mem_filter.mp ha).1
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact (List.mem_filter.mp (List.of_mem_zip (List.mem_filter.mp hb).1).1).1

theorem rewrite_syntax (D : Nat) (r : Row) (labels : List Nat) (removed : Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r) :
    RowAllowed D (rewrite D (canonicalRow r) labels removed) ∧
      NamesFrom (rowVariables r) (rewrite D (canonicalRow r) labels removed) := by
  have hrep := classReplacement_syntax D r _ hDegree hD (class_item_current r labels removed)
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact canonical_allowed D r hD a (outside_subset _ labels removed a ha)
    · exact hrep.1 a ha
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    rcases List.mem_append.mp ha with ha | ha
    · exact canonical_names r a.2.1
        (List.mem_map.mpr ⟨a,outside_subset _ labels removed a ha,rfl⟩)
    · exact hrep.2 a.2.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)

/-- Unconditional guard admission and maximum-linearity follow at a constant
paid valuation; original-name support follows directly from emitted syntax. -/
theorem partitionGuard_syntax (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r) :
    Formula.allowed D (partitionGuard D maximum (canonicalRow r) labels) ∧
      linear maximum (partitionGuard D maximum (canonicalRow r) labels) = true ∧
      FormulaNamesFrom (rowVariables r) (partitionGuard D maximum (canonicalRow r) labels) := by
  have hf := partitionGuard_facts D maximum r labels hDegree hD
    (fun _ => partitionTail D maximum (canonicalRow r))
    (fun a ha => ⟨le_rfl,le_rfl⟩)
  refine ⟨hf.1,hf.2.2.1,?_⟩
  intro i hi
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
  change t ∈ Formula.tokens (conjoin _) at ht
  rw [conjoin_tokens] at ht
  obtain ⟨p,hp,htp⟩ := List.mem_flatMap.mp ht
  obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  have hn := comparisonGuard_names D maximum (leader a.1) (leader b.1)
    (FullWordGuardCompletion.orderNat a.2 b.2) t.1 (List.mem_map.mpr ⟨t,htp,rfl⟩)
  have hna : (leader a.1).1 ∈ rowVariables r := canonical_names r a.1.2.1
    (List.mem_map.mpr ⟨a.1,(List.mem_filter.mp (List.of_mem_zip ha).1).1,rfl⟩)
  have hnb : (leader b.1).1 ∈ rowVariables r := canonical_names r b.1.2.1
    (List.mem_map.mpr ⟨b.1,(List.mem_filter.mp (List.of_mem_zip hb).1).1,rfl⟩)
  rcases hn with hn | hn
  · rwa [hn]
  · rwa [hn]

theorem intrinsicStageSyntaxAndDecrease : AlgorithmTargets.IntrinsicStageSyntaxAndDecrease := by
  intro D maximum r hDegree hD b hb
  by_cases hm : hasMaximum maximum (canonicalRow r) = true
  · have hstage : b ∈ (assignments (active (canonicalRow r)).length
        (active (canonicalRow r)).length).map (fun labels =>
          let out := partitionBranch D maximum (canonicalRow r) labels
          {out with tail := max (rowTail r) out.tail}) := by simpa [stage,hm] using hb
    obtain ⟨labels,hlabels,rfl⟩ := List.mem_map.mp hstage
    have hlen := (assignments_membership _ _ _).mp hlabels |>.1
    have hguard := partitionGuard_syntax D maximum r labels hDegree hD
    cases hz : zeroClass (canonicalRow r) labels with
    | none =>
        have htag : (if leading ((classes (canonicalRow r) labels).getLastD []) < 0
            then (0 : Nat) else 2) = 0 ∨
            (if leading ((classes (canonicalRow r) labels).getLastD []) < 0
            then (0 : Nat) else 2) = 2 := by split <;> simp
        simp only [partitionBranch,hz,BranchSyntax]
        exact ⟨⟨hguard.1,hguard.2.1,hguard.2.2,by simp [RowAllowed],
          by simp [NamesFrom,rowVariables],htag.elim Or.inl (fun h => Or.inr (Or.inl h))⟩,True.intro⟩
    | some removed =>
        have hsome := zeroClass_some_data (canonicalRow r) labels removed hz
        have hrewrite := rewrite_syntax D r labels removed hDegree hD
        simp only [partitionBranch,hz,BranchSyntax]
        exact ⟨⟨hguard.1,hguard.2.1,hguard.2.2,hrewrite.1,hrewrite.2⟩,
          rewrite_decrease D r labels removed hDegree hD hlen hsome.2.1⟩
  · have hf : hasMaximum maximum (canonicalRow r) = false := Bool.eq_false_of_not_eq_true hm
    have he : b = ⟨max (rowTail r) (rowSourceTail (canonicalRow r)),.top,.finish ⟨3,canonicalRow r⟩⟩ := by
      simpa [stage,hf] using hb
    subst b
    simp only [BranchSyntax]
    refine ⟨⟨?_,?_,?_,canonical_allowed D r hD,canonical_names r,
      Or.inr (Or.inr ⟨rfl,canonical_maximum_absent maximum r hf⟩)⟩,True.intro⟩
    · simp [Formula.allowed,Formula.tokens,LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
    · rfl
    · simp [FormulaNamesFrom,Formula.variables,Formula.tokens,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof

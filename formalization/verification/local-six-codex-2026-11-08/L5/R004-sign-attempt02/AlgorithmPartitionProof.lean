module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmItemProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmLabelsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.GuardStatementChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm
open LogicLineages.ModelsAlgebra.Forests

theorem conjoin_tokens (ps : List Formula) :
    Formula.tokens (conjoin ps) = ps.flatMap Formula.tokens := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa [conjoin,Formula.tokens,CotreePresburgerUnit.Boolean.atoms,List.flatMap_append]
        using congrArg (List.append (Formula.tokens p)) ih

theorem conjoin_eval (ps : List Formula) (ν : Nat → Nat) :
    Formula.eval ν (conjoin ps) ↔ ∀ p ∈ ps, Formula.eval ν p := by
  induction ps with
  | nil => simp [conjoin,Formula.eval]
  | cons p ps ih => simp [conjoin,Formula.eval,← ih]

theorem disjoin_token_member (ps : List Formula) (t : Token)
    (ht : t ∈ Formula.tokens (disjoin ps)) :
    ∃ p ∈ ps, t ∈ Formula.tokens p := by
  induction ps with
  | nil => simp [disjoin,Formula.tokens,CotreePresburgerUnit.Boolean.atoms] at ht
  | cons p ps ih =>
      have hm : t ∈ Formula.tokens p ∨ t ∈ Formula.tokens (disjoin ps) := by
        simpa [disjoin,Formula.tokens,CotreePresburgerUnit.Boolean.atoms,
          List.flatMap_append] using ht
      rcases hm with hm | hm
      · exact ⟨p,by simp,hm⟩
      · obtain ⟨q,hq,htq⟩ := ih hm
        exact ⟨q,by simp [hq],htq⟩

theorem signFormula_names (s : Nat) (r : Row) (i : Nat)
    (hi : i ∈ Formula.variables (signFormula s r)) : i ∈ rowVariables r := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (GuardProof.signFormula_tokens_subset s r t ht)
  exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem orderedGuard_names (D : Nat) (u v : Token) (desired i : Nat)
    (hi : i ∈ Formula.variables (orderedGuard D u v desired)) : i = u.1 ∨ i = v.1 := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
  obtain ⟨p,hp,htp⟩ := disjoin_token_member _ t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  have hn := signFormula_names s (renamePairRow u.1 v.1
    (FullWordGuardCompletion.packageRow (FullWordGuardCompletion.compile D (u.2,v.2))))
    t.1 (List.mem_map.mpr ⟨t,htp,rfl⟩)
  obtain ⟨a,ha,hname⟩ := List.mem_map.mp hn
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  by_cases hz : b.2.1 = 0 <;> simp [renamePairRow,hz] at hname <;> omega

theorem comparisonGuard_names (D maximum : Nat) (u v : Token) (desired i : Nat)
    (hi : i ∈ Formula.variables (comparisonGuard D maximum u v desired)) :
    i = u.1 ∨ i = v.1 := by
  by_cases hu : u.1 = maximum
  · by_cases hv : v.1 = maximum
    · by_cases hs : FullWordGuardCompletion.packageSame
          (FullWordGuardCompletion.compile D (u.2,v.2)) = desired <;>
        simp [comparisonGuard,hu,hv,hs,Formula.variables,Formula.tokens,
          CotreePresburgerUnit.Boolean.atoms] at hi
    · exact orderedGuard_names D u v desired i (by simpa [comparisonGuard,hu,hv] using hi)
  · by_cases hv : v.1 = maximum
    · exact (orderedGuard_names D v u (FullWordGuardCompletion.reverseOrder desired) i
        (by simpa [comparisonGuard,hu,hv] using hi)).symm
    · have hm := signFormula_names desired (literalDifference u v) i
        (by simpa [comparisonGuard,hu,hv] using hi)
      simpa [rowVariables,literalDifference] using hm

theorem pairCutoff_le_partitionTail (D maximum : Nat) (r : Row) (a b : Item)
    (ha : a ∈ active r) (hb : b ∈ active r) :
    comparisonCutoff D maximum (leader a) (leader b) ≤ partitionTail D maximum r := by
  apply (member_le_foldMax _ _ ?_).trans (Nat.le_max_right _ _)
  exact List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

theorem orderNat_bound (a b : Nat) : FullWordGuardCompletion.orderNat a b ≤ 2 := by
  unfold FullWordGuardCompletion.orderNat
  split_ifs <;> omega

/-- All ordered-partition guard domains are paid, including inconsistent
partitions. Truth then states exactly the ordering of the actual leaders. -/
theorem partitionGuard_facts (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r) (ν : Nat → Nat)
    (ht : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum) :
    Formula.allowed D (partitionGuard D maximum (canonicalRow r) labels) ∧
    Formula.meaningful (partitionGuard D maximum (canonicalRow r) labels) ν ∧
    linear maximum (partitionGuard D maximum (canonicalRow r) labels) = true ∧
    (Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels) ↔
      ∀ a ∈ labelled (canonicalRow r) labels, ∀ b ∈ labelled (canonicalRow r) labels,
        FullWordGuardCompletion.orderNat
          (wordValue (leader a.1).2 (ν a.1.2.1))
          (wordValue (leader b.1).2 (ν b.1.2.1)) =
            FullWordGuardCompletion.orderNat a.2 b.2) := by
  let zs := labelled (canonicalRow r) labels
  let guards := zs.flatMap (fun a => zs.map (fun b =>
    comparisonGuard D maximum (leader a.1) (leader b.1)
      (FullWordGuardCompletion.orderNat a.2 b.2)))
  have hpairs : ∀ a ∈ zs, ∀ b ∈ zs,
      Formula.allowed D (comparisonGuard D maximum (leader a.1) (leader b.1)
        (FullWordGuardCompletion.orderNat a.2 b.2)) ∧
      Formula.meaningful (comparisonGuard D maximum (leader a.1) (leader b.1)
        (FullWordGuardCompletion.orderNat a.2 b.2)) ν ∧
      linear maximum (comparisonGuard D maximum (leader a.1) (leader b.1)
        (FullWordGuardCompletion.orderNat a.2 b.2)) = true ∧
      (Formula.eval ν (comparisonGuard D maximum (leader a.1) (leader b.1)
        (FullWordGuardCompletion.orderNat a.2 b.2)) ↔
        FullWordGuardCompletion.orderNat
          (wordValue (leader a.1).2 (ν a.1.2.1))
          (wordValue (leader b.1).2 (ν b.1.2.1)) =
            FullWordGuardCompletion.orderNat a.2 b.2) := by
    intro a ha b hb
    have ha' := (List.of_mem_zip ha).1
    have hb' := (List.of_mem_zip hb).1
    have hab := pairCutoff_le_partitionTail D maximum (canonicalRow r) a.1 b.1 ha' hb'
    have hn := GuardProof.namedMaximumComparison D maximum (leader a.1) (leader b.1)
      (FullWordGuardCompletion.orderNat a.2 b.2) hDegree
      (leader_allowed D r a.1 hD ha') (leader_allowed D r b.1 hD hb')
      (orderNat_bound _ _) ν (hab.trans (ht a.1 ha').1) (hab.trans (ht b.1 hb').1)
      (ht a.1 ha').2 (ht b.1 hb').2
    simpa [leader] using hn.2.2
  have hguards : ∀ p ∈ guards, Formula.allowed D p ∧ Formula.meaningful p ν ∧
      linear maximum p = true := by
    intro p hp
    obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact ⟨(hpairs a ha b hb).1,(hpairs a ha b hb).2.1,(hpairs a ha b hb).2.2.1⟩
  change Formula.allowed D (conjoin guards) ∧ Formula.meaningful (conjoin guards) ν ∧
    linear maximum (conjoin guards) = true ∧ _
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht'
    rw [conjoin_tokens] at ht'
    obtain ⟨p,hp,htp⟩ := List.mem_flatMap.mp ht'
    exact (hguards p hp).1 t htp
  · intro t ht'
    rw [conjoin_tokens] at ht'
    obtain ⟨p,hp,htp⟩ := List.mem_flatMap.mp ht'
    exact (hguards p hp).2.1 t htp
  · apply List.all_eq_true.mpr
    intro t ht'
    rw [conjoin_tokens] at ht'
    obtain ⟨p,hp,htp⟩ := List.mem_flatMap.mp ht'
    exact List.all_eq_true.mp (hguards p hp).2.2 t htp
  · rw [conjoin_eval]
    constructor
    · intro he a ha b hb
      apply (hpairs a ha b hb).2.2.2.mp
      exact he _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)
    · intro he p hp
      obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
      exact (hpairs a ha b hb).2.2.2.mpr (he a ha b hb)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof

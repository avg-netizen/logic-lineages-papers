module
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosTargets
public import LogicLineages.OrdinalComparison.CollectedFiniteTailProof
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeProof
public import LogicLineages.OrdinalComparison.PositiveInputPlugProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem positive_zero_bound_computable : Computable₂ encodedPositiveZeroBound := by
  have hn : Computable (fun p : Nat × Nat => encodedCollectedNormalize p.1) :=
    encodedCollectedNormalizeComputable.comp Computable.fst
  have hm : Computable (fun p : Nat × Nat => encodedCollectedNormalize p.2) :=
    encodedCollectedNormalizeComputable.comp Computable.snd
  exact encodedCollectedZeroBoundPrimitiveRecursive.to_comp.comp
    (Computable.list_cons.comp hn (Computable.list_cons.comp hm (Computable.const [])))

private theorem computable_if {α β : Type} [Primcodable α] [Primcodable β]
    (p : α → Prop) [DecidablePred p] (f g : α → β)
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp hf hg

private theorem equality_prefix_step_computable : Computable₂
    (fun p : Nat × Nat => fun q : Nat × List Nat => q.2 ++
      if 0<q.1 ∧ encodedPositiveEvaluation p.1 q.1=encodedPositiveEvaluation p.2 q.1 then [q.1] else []) := by
  have hn : Computable (fun z : (Nat × Nat) × (Nat × List Nat) => z.1.1) := Computable.fst.comp Computable.fst
  have hm : Computable (fun z : (Nat × Nat) × (Nat × List Nat) => z.1.2) := Computable.snd.comp Computable.fst
  have hk : Computable (fun z : (Nat × Nat) × (Nat × List Nat) => z.2.1) := Computable.fst.comp Computable.snd
  have hl : Computable (fun z : (Nat × Nat) × (Nat × List Nat) => z.2.2) := Computable.snd.comp Computable.snd
  have hvn := encodedPositiveEvaluationComputable.comp hn hk
  have hvm := encodedPositiveEvaluationComputable.comp hm hk
  have heqbase : Primrec (fun p : Nat × Nat => decide (p.1=p.2)) := Primrec.eq.decide
  have heq := heqbase.to_comp.comp (hvn.pair hvm)
  have hpos : Computable (fun z : (Nat × Nat) × (Nat × List Nat) => decide (0<z.2.1)) :=
    (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)).decide.to_comp
  have hsingle := Computable.list_cons.comp hk (Computable.const ([] : List Nat))
  have hinner := computable_if _ _ _ heq hsingle (Computable.const ([] : List Nat))
  have houter := computable_if _ _ _ hpos hinner (Computable.const ([] : List Nat))
  have h := Computable.list_append.comp hl houter
  apply h.of_eq
  intro z
  by_cases hp : 0<z.2.1 <;>
    by_cases he : encodedPositiveEvaluation z.1.1 z.2.1=encodedPositiveEvaluation z.1.2 z.2.1 <;>
    simp [hp,he]

private theorem equality_prefix_computable : Computable₂
    (fun p : Nat × Nat => encodedPositiveEqualityPrefix p.1 p.2) := by
  have hs : Computable₂ (fun p : (Nat × Nat) × Nat => fun q : Nat × List Nat => q.2 ++
      if 0<q.1 ∧ encodedPositiveEvaluation p.1.1 q.1=encodedPositiveEvaluation p.1.2 q.1 then [q.1] else []) :=
    equality_prefix_step_computable.comp (Computable.fst.comp Computable.fst) Computable.snd
  have ht := Computable.nat_rec (Computable.snd : Computable (fun p : (Nat × Nat) × Nat => p.2))
    (Computable.const ([] : List Nat)) hs
  apply ht.of_eq
  intro p
  rcases p with ⟨⟨n,m⟩,k⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.rec (motive := fun _ => List Nat) [] (fun j acc => acc ++
      if 0<j ∧ encodedPositiveEvaluation n j=encodedPositiveEvaluation m j then [j] else []) k ++
      (if 0<k ∧ encodedPositiveEvaluation n k=encodedPositiveEvaluation m k then [k] else []) = _
    change Nat.rec (motive := fun _ => List Nat) [] (fun j acc => acc ++
      if 0<j ∧ encodedPositiveEvaluation n j=encodedPositiveEvaluation m j then [j] else []) k = _ at ih
    rw [ih]
    rfl

private theorem equality_set_computable : Computable₂ encodedPositiveEqualitySet :=
  equality_prefix_computable.comp Computable.id positive_zero_bound_computable

private theorem equality_prefix_membership (n m k x : Nat) :
    x∈encodedPositiveEqualityPrefix n m k ↔
      0<x ∧ x<k ∧ encodedPositiveEvaluation n x=encodedPositiveEvaluation m x := by
  induction k with
  | zero => simp [encodedPositiveEqualityPrefix]
  | succ k ih =>
    rw [encodedPositiveEqualityPrefix,List.mem_append]
    by_cases hk : 0<k ∧ encodedPositiveEvaluation n k=encodedPositiveEvaluation m k
    · rw [if_pos hk]
      simp only [List.mem_singleton,ih]
      constructor
      · rintro (h | rfl)
        · exact ⟨h.1,Nat.lt_succ_of_lt h.2.1,h.2.2⟩
        · exact ⟨hk.1,Nat.lt_succ_self _,hk.2⟩
      · intro h
        by_cases he : x=k
        · exact Or.inr he
        · exact Or.inl ⟨h.1,by omega,h.2.2⟩
    · rw [if_neg hk]
      simp only [List.not_mem_nil,or_false,ih]
      constructor
      · intro h; exact ⟨h.1,Nat.lt_succ_of_lt h.2.1,h.2.2⟩
      · intro h
        have hne : x≠k := by intro he; subst x; exact hk ⟨h.1,h.2.2⟩
        exact ⟨h.1,by omega,h.2.2⟩

private theorem equality_prefix_nodup (n m k : Nat) : (encodedPositiveEqualityPrefix n m k).Nodup := by
  induction k with
  | zero => simp [encodedPositiveEqualityPrefix]
  | succ k ih =>
    rw [encodedPositiveEqualityPrefix]
    split
    · apply List.nodup_append.mpr
      refine ⟨ih,by simp,?_⟩
      intro a ha b hb hab
      have hlt := ((equality_prefix_membership n m k a).mp ha).2.1
      have hb' : b=k := by simpa using hb
      subst b
      omega
    · simpa using ih

theorem fullActualPositiveFiniteZeros : Targets.FullActualPositiveFiniteZeros := by
  refine ⟨positive_zero_bound_computable,equality_set_computable,?_⟩
  intro E F hvE hvF
  let n := positiveExprEncode E
  let m := positiveExprEncode F
  let N := encodedPositiveZeroBound n m
  let A := collectedPositiveNormalize E
  let B := collectedPositiveNormalize F
  have hA : CollectedPositiveValid A := collectedPositiveNormalizeValid E hvE
  have hB : CollectedPositiveValid B := collectedPositiveNormalizeValid F hvF
  have hv : ∀ C∈[A,B], CollectedPositiveValid C := by
    intro C hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl
    · exact hA
    · exact hB
  have hN : N=collectedFiniteZeroBound [A,B] := by
    dsimp only [N,n,m,encodedPositiveZeroBound]
    rw [encodedCollectedNormalizeCorrect E hvE,encodedCollectedNormalizeCorrect F hvF]
    exact encodedCollectedZeroBoundCorrect [A,B]
  have hNpos : 1≤N := by
    rw [hN]
    have h4 : 4≤collectedFiniteZeroBound [A,B] :=
      (le_max_left _ _).trans (le_max_right _ _)
    omega
  have hclosure := collectedFiniteClosureDomain [A,B] hv
  have hAmem := hclosure.2.1 A List.mem_cons_self
  have hBmem := hclosure.2.1 B (by simp)
  have htail : A≠B → ∀ x : Nat, N≤x → actualFixedLimitProfileEval E x≠actualFixedLimitProfileEval F x := by
    intro hne x hx heq
    have hs := collectedFiniteTailSeparation [A,B] hv x (by simpa only [hN] using hx) A hAmem B hBmem
    apply hne
    apply hs.mp
    change actualCollectedPositiveEval (collectedPositiveNormalize E) x=
      actualCollectedPositiveEval (collectedPositiveNormalize F) x
    rw [collectedPositiveNormalizeValue E hvE x,collectedPositiveNormalizeValue F hvF x]
    exact heq
  have hmember : ∀ x : Nat, x∈encodedPositiveEqualitySet n m ↔
      0<x ∧ x<N ∧ actualFixedLimitProfileEval E x=actualFixedLimitProfileEval F x := by
    intro x
    have h := equality_prefix_membership n m N x
    dsimp only [n,m] at h
    rw [encodedPositiveEvaluationCorrect E x,encodedPositiveEvaluationCorrect F x] at h
    exact h
  refine ⟨hNpos,?_,?_,equality_prefix_nodup n m N,hmember⟩
  · intro heq x
    rw [← collectedPositiveNormalizeValue E hvE x,← collectedPositiveNormalizeValue F hvF x,heq]
  · intro hne
    refine ⟨htail hne,?_⟩
    intro x hx
    constructor
    · intro heq
      apply (hmember x).mpr
      have hlt : x<N := by
        by_contra h
        exact htail hne x (Nat.le_of_not_gt h) heq
      exact ⟨hx,hlt,heq⟩
    · intro hm
      exact ((hmember x).mp hm).2.2

end LogicLineages.OrdinalComparison

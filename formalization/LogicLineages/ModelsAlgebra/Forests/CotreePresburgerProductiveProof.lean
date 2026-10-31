module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductiveTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVectorStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjectionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive.Proof
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open CotreePresburgerBoolean CotreePresburgerProduct CotreePresburgerPullback CotreePresburgerCountVector

variable {Q : Type} [Fintype Q] [LinearOrder Q]

theorem word_total (xs : List Q) : (∑ q, wordCounts xs q) = xs.length := by
  calc
    _ = ∑ q, xs.count q := by
      apply Finset.sum_congr rfl
      intro q _
      exact CotreePresburgerPullback.StatementChecks.wordCountsEqCount Q xs q
    _ = _ := CotreePresburgerProjection.StatementChecks.wordTotalCounts Q xs

theorem word_zero (xs : List Q) (q : Q) : wordCounts xs q = 0 ↔ q ∉ xs := by
  rw [CotreePresburgerPullback.StatementChecks.wordCountsEqCount Q xs q]
  exact List.count_eq_zero

theorem enabledListExact : Targets.EnabledListExact := by
  intro Q _ _ A R q
  constructor
  · rintro ⟨o,c,hc,htotal,hsupport⟩
    obtain ⟨n,v,hv⟩ := CotreePresburgerCountVector.StatementChecks.childrenExact Q c htotal
    have hcounts : wordCounts (List.ofFn v) = c := by
      rw [hv]
      exact CotreePresburgerCountVector.StatementChecks.countsExact Q c
    refine ⟨o,n,v,?_,?_⟩
    · intro i
      have hm : v i ∈ realizeCounts c := by
        rw [← hv]
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
      have hp := (CotreePresburgerCountVector.StatementChecks.membershipExact Q c (v i)).mp hm
      by_contra hn
      have hz := hsupport (v i) hn
      omega
    · rw [hcounts]
      exact hc
  · rintro ⟨o,n,v,hv,hs⟩
    refine ⟨o,wordCounts (List.ofFn v),hs,?_,?_⟩
    · rw [word_total,List.length_ofFn]
      omega
    · intro q hq
      apply (word_zero _ q).mpr
      intro hm
      rcases List.mem_ofFn.mp hm with ⟨i,rfl⟩
      exact hq (hv i)

theorem height_pos (C : Cotree) : 0 < height C := by
  cases C <;> simp [height]

theorem mem_step (A : Automaton Q) (R : Finset Q) q :
    q ∈ step A R ↔ q ∈ R ∨ q = A.leaf ∨ Enabled A R q := by
  classical
  simp [step,or_assoc,or_left_comm]

theorem subset_step (A : Automaton Q) (R : Finset Q) : R ⊆ step A R :=
  fun q h => (mem_step A R q).mpr (Or.inl h)

theorem reachableHeightExact : Targets.ReachableHeightExact := by
  intro Q _ _ A n
  classical
  induction n with
  | zero =>
    intro q
    constructor
    · simp [reachable]
    · rintro ⟨C,hC,_⟩
      have hp := height_pos C
      omega
  | succ n ih =>
    intro q
    change q ∈ step A (reachable A n) ↔ _
    rw [mem_step]
    constructor
    · rintro (hq | hq | he)
      · obtain ⟨C,hC,hr⟩ := (ih q).mp hq
        exact ⟨C,by omega,hr⟩
      · subst q
        exact ⟨.atom,by simp [height],Runs.atom⟩
      · obtain ⟨o,k,v,hv,hs⟩ := (enabledListExact Q A _ q).mp he
        have hex : ∀ i, ∃ C, height C ≤ n ∧ Runs A C (v i) := fun i => (ih _).mp (hv i)
        let c : Fin (k+2) → Cotree := fun i => Classical.choose (hex i)
        have hh : ∀ i, height (c i) ≤ n := fun i => (Classical.choose_spec (hex i)).1
        have hr : ∀ i, Runs A (c i) (v i) := fun i => (Classical.choose_spec (hex i)).2
        refine ⟨.node o k c,?_,Runs.node v q hr hs⟩
        change Finset.univ.sup (fun i => height (c i)) + 1 ≤ n+1
        exact Nat.add_le_add_right (Finset.sup_le (fun i _ => hh i)) 1
    · rintro ⟨C,hC,hr⟩
      cases C with
      | atom => cases hr; exact Or.inr (Or.inl rfl)
      | node o k c =>
        cases hr with
        | node v q children stepH =>
          have hsup : Finset.univ.sup (fun i => height (c i)) ≤ n := by
            change Finset.univ.sup (fun i => height (c i)) + 1 ≤ n+1 at hC
            omega
          have hh : ∀ i, height (c i) ≤ n := fun i =>
            (Finset.le_sup (Finset.mem_univ i)).trans hsup
          exact Or.inr (Or.inr ((enabledListExact Q A _ q).mpr
            ⟨o,k,v,fun i => (ih _).mpr ⟨c i,hh i,children i⟩,stepH⟩))

theorem saturation : Targets.Saturation := by
  intro Q _ _ A
  have grow : ∀ n, reachable A n = reachable A (n+1) ∨ n < (reachable A (n+1)).card := by
    intro n
    induction n with
    | zero =>
      by_cases he : reachable A 0 = reachable A 1
      · exact Or.inl he
      · right
        apply Finset.card_pos.mpr
        apply Finset.nonempty_iff_ne_empty.mpr
        intro h
        exact he h.symm
    | succ n ih =>
      rcases ih with he | hc
      · exact Or.inl (congrArg (step A) he)
      · by_cases he : reachable A (n+1) = reachable A (n+1+1)
        · exact Or.inl he
        · right
          have hlt := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step A _,he⟩)
          change (reachable A (n+1)).card < (reachable A (n+1+1)).card at hlt
          omega
  rcases grow (Fintype.card Q) with he | hc
  · exact he.symm
  · have hb : (reachable A (Fintype.card Q+1)).card ≤ Fintype.card Q := Finset.card_le_univ _
    omega

theorem all_runs_reachable (A : Automaton Q) {C q} (h : Runs A C q) :
    q ∈ reachable A (Fintype.card Q) := by
  have hs := saturation Q A
  induction h with
  | atom =>
    rw [← hs]
    exact (mem_step A _ _).mpr (Or.inr (Or.inl rfl))
  | @node o n c v q children stepH ih =>
    rw [← hs]
    exact (mem_step A _ _).mpr (Or.inr (Or.inr
      ((enabledListExact Q A _ q).mpr ⟨o,n,v,ih,stepH⟩)))

theorem runProductiveExact : Targets.RunProductiveExact := by
  intro Q _ _ A q
  constructor
  · intro h
    obtain ⟨C,_,hr⟩ := (reachableHeightExact Q A (Fintype.card Q) q).mp h
    exact ⟨C,hr⟩
  · rintro ⟨C,hr⟩
    exact all_runs_reachable A hr

theorem acceptingProductiveExact : Targets.AcceptingProductiveExact := by
  intro Q _ _ A
  constructor
  · rintro ⟨C,q,hr,ha⟩
    exact ⟨q,(runProductiveExact Q A q).mpr ⟨C,hr⟩,ha⟩
  · rintro ⟨q,hq,ha⟩
    obtain ⟨C,hr⟩ := (runProductiveExact Q A q).mp hq
    exact ⟨C,q,hr,ha⟩

theorem empty_productive (A : Automaton Q) (hred : ∀ C q, Runs A C q → Reduced C) :
    Empty A ↔ ∀ q ∈ productive A, A.accept q = false := by
  constructor
  · intro he q hq
    obtain ⟨C,hr⟩ := (runProductiveExact Q A q).mp hq
    cases ha : A.accept q with
    | false => rfl
    | true => exact (he C ⟨hred C q hr,q,hr,ha⟩).elim
  · intro hp C hC
    obtain ⟨_,q,hr,ha⟩ := hC
    have hf := hp q ((runProductiveExact Q A q).mpr ⟨C,hr⟩)
    simp [ha] at hf

theorem runs_transport (T : Type) (d e : DecidableEq T) (A : Automaton T) C q
    (h : @Runs T d A C q) : @Runs T e A C q := by
  cases Subsingleton.elim d e
  exact h

theorem characterization_transport (T : Type) [Fintype T] (d e : DecidableEq T) (A : Automaton T)
    (h : @Empty T d A ↔ ∀ q ∈ @productive T _ d A, A.accept q = false) :
    @Empty T e A ↔ ∀ q ∈ @productive T _ e A, A.accept q = false := by
  cases Subsingleton.elim d e
  exact h

theorem sourceDifferenceEmptyExact : Targets.SourceDifferenceEmptyExact := by
  intro M N _ _
  let D := difference (source M) (source N)
  have hred : ∀ C q, Runs D C q → Reduced C := by
    intro C q h
    have hp := (CotreePresburgerProduct.StatementChecks.productRunsExact _ _
      (source M) (complement (source N)) C q).mp (runs_transport _ _ _ _ _ _ h)
    have hs := (CotreePresburgerBoolean.StatementChecks.sourceRunsExact M C _).mp
      (runs_transport _ _ _ _ _ _ hp.1)
    exact ((CotreePresburgerAutomaton.StatementChecks.runsExact M C _).mp hs).1
  have hc := empty_productive D (fun C q h => hred C q (runs_transport _ _ _ _ _ _ h))
  exact characterization_transport _ _ _ D hc

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive.Proof

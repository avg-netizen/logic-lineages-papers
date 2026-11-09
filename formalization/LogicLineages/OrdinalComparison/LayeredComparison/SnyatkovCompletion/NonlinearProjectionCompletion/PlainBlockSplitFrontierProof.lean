module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitStateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

def GoodState (s : State) : Prop :=
  s.1.Nodup ∧ TiedLinear.allowed s.1 s.2 = true ∧ ParametersIndependent s.1 s.2
def GoodFrontier (states : List State) : Prop := ∀ s ∈ states, GoodState s
def FrontierMeaning (ν : Nat → Nat) (states : List State) : Prop :=
  ∃ s ∈ states, existsPrefix ν s.1 s.2

theorem mem_advance (states : List State) (q : State) :
    q ∈ advance states ↔ ∃ s ∈ states,
      (s.1 = [] ∧ q = s) ∨ (s.1 ≠ [] ∧ q ∈ branches s.1 s.2) := by
  constructor
  · intro hq
    obtain ⟨s, hs, hinner⟩ := List.mem_flatMap.mp hq
    refine ⟨s, hs, ?_⟩
    by_cases he : s.1 = []
    · rw [if_pos he] at hinner
      exact Or.inl ⟨he, List.mem_singleton.mp hinner⟩
    · rw [if_neg he] at hinner
      exact Or.inr ⟨he, hinner⟩
  · rintro ⟨s, hs, (⟨he, hq⟩ | ⟨he, hq⟩)⟩
    · subst q
      exact List.mem_flatMap.mpr ⟨s, hs, by rw [if_pos he]; exact List.mem_singleton_self _⟩
    · exact List.mem_flatMap.mpr ⟨s, hs, by rw [if_neg he]; exact hq⟩

theorem advance_good (states : List State) (hgood : GoodFrontier states) :
    GoodFrontier (advance states) := by
  intro q hq
  obtain ⟨s, hs, hcase⟩ := (mem_advance states q).mp hq
  have hg := hgood s hs
  rcases hcase with ⟨_, rfl⟩ | ⟨_, hbranch⟩
  · exact hg
  · obtain ⟨i, _, he⟩ := branches_erase_bound s.1 s.2 q hbranch
    have hnd : q.1.Nodup := by rw [he]; exact hg.1.erase i
    have hc := wholeBlockStateClosure s.1 s.2 hg.2.1 hg.2.2 q hbranch
    exact ⟨hnd, hc.1, hc.2⟩

theorem advance_meaning (states : List State) (hgood : GoodFrontier states) (ν : Nat → Nat) :
    FrontierMeaning ν (advance states) ↔ FrontierMeaning ν states := by
  constructor
  · rintro ⟨q, hq, hp⟩
    obtain ⟨s, hs, hcase⟩ := (mem_advance states q).mp hq
    have hg := hgood s hs
    refine ⟨s, hs, ?_⟩
    rcases hcase with ⟨_, rfl⟩ | ⟨hne, hbranch⟩
    · exact hp
    · exact (actualOneStepProjection s.1 s.2 hg.1 hne hg.2.1 hg.2.2 ν).mpr ⟨q, hbranch, hp⟩
  · rintro ⟨s, hs, hp⟩
    have hg := hgood s hs
    by_cases he : s.1 = []
    · exact ⟨s, (mem_advance states s).mpr ⟨s, hs, Or.inl ⟨he, rfl⟩⟩, hp⟩
    · obtain ⟨q, hbranch, hq⟩ := (actualOneStepProjection s.1 s.2 hg.1 he hg.2.1 hg.2.2 ν).mp hp
      exact ⟨q, (mem_advance states q).mpr ⟨s, hs, Or.inr ⟨he, hbranch⟩⟩, hq⟩

theorem run_succ (fuel : Nat) (states : List State) :
    run (fuel + 1) states = run fuel (advance states) :=
  Function.iterate_succ_apply advance fuel states

theorem run_good (fuel : Nat) (states : List State) (hgood : GoodFrontier states) :
    GoodFrontier (run fuel states) := by
  induction fuel generalizing states with
  | zero => exact hgood
  | succ fuel ih =>
    rw [run_succ]
    exact ih (advance states) (advance_good states hgood)

theorem run_meaning (fuel : Nat) (states : List State) (hgood : GoodFrontier states) (ν : Nat → Nat) :
    FrontierMeaning ν (run fuel states) ↔ FrontierMeaning ν states := by
  induction fuel generalizing states with
  | zero => rfl
  | succ fuel ih =>
    rw [run_succ]
    exact (ih (advance states) (advance_good states hgood)).trans (advance_meaning states hgood ν)

theorem advance_length_bound (fuel : Nat) (states : List State)
    (hlen : ∀ s ∈ states, s.1.length ≤ fuel + 1) :
    ∀ q ∈ advance states, q.1.length ≤ fuel := by
  intro q hq
  obtain ⟨s, hs, hcase⟩ := (mem_advance states q).mp hq
  rcases hcase with ⟨he, rfl⟩ | ⟨_, hbranch⟩
  · rw [he]
    exact Nat.zero_le _
  · have hlt := strictOriginalBoundDecrease s.1 s.2 q hbranch
    have hslen := hlen s hs
    omega

theorem run_finishes (fuel : Nat) (states : List State)
    (hlen : ∀ s ∈ states, s.1.length ≤ fuel) : ∀ s ∈ run fuel states, s.1 = [] := by
  induction fuel generalizing states with
  | zero =>
    intro s hs
    have h := hlen s hs
    exact List.length_eq_zero_iff.mp (by omega)
  | succ fuel ih =>
    rw [run_succ]
    exact ih (advance states) (advance_length_bound fuel states hlen)

theorem advance_parameter_support (states : List State) (q : State) (hq : q ∈ advance states)
    (j : Nat) (hj : j ∈ q.2.parameters) : ∃ s ∈ states, j ∈ s.2.parameters := by
  obtain ⟨s, hs, hcase⟩ := (mem_advance states q).mp hq
  refine ⟨s, hs, ?_⟩
  rcases hcase with ⟨_, rfl⟩ | ⟨_, hbranch⟩
  · exact hj
  · exact branch_parameter_support s.1 s.2 q hbranch j hj

theorem run_parameter_support (fuel : Nat) (states : List State) (q : State)
    (hq : q ∈ run fuel states) (j : Nat) (hj : j ∈ q.2.parameters) :
    ∃ s ∈ states, j ∈ s.2.parameters := by
  induction fuel generalizing states with
  | zero => exact ⟨q, hq, hj⟩
  | succ fuel ih =>
    rw [run_succ] at hq
    obtain ⟨s, hs, hjs⟩ := ih (advance states) hq
    exact advance_parameter_support states s hs j hjs

theorem initial_good (bound : List Nat) (p : Formula) (hnd : bound.Nodup)
    (ha : TiedLinear.allowed bound p = true) (hp : ParametersIndependent bound p) :
    GoodFrontier [(bound, p)] := by
  intro s hs
  have he : s = (bound, p) := List.mem_singleton.mp hs
  subst s
  exact ⟨hnd, ha, hp⟩

theorem project_meaning (bound : List Nat) (p : Formula) (ν : Nat → Nat) :
    (project bound p).eval ν ↔ FrontierMeaning ν (run bound.length [(bound, p)]) := by
  have hfinish : ∀ s ∈ run bound.length [(bound, p)], s.1 = [] := by
    apply run_finishes
    intro s hs
    have he : s = (bound, p) := List.mem_singleton.mp hs
    subst s
    exact le_rfl
  rw [project, WindowProof.any_truth]
  constructor
  · rintro ⟨q, hq, htruth⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    refine ⟨s, hs, ?_⟩
    rw [hfinish s hs]
    exact (BlockRowsProof.actualExpandedCompilation s.2 ν).mp htruth
  · rintro ⟨s, hs, hp⟩
    refine ⟨s.2.compile, List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
    apply (BlockRowsProof.actualExpandedCompilation s.2 ν).mpr
    simpa only [hfinish s hs, existsPrefix] using hp

/-- The actual fixed-length frontier is a uniform parameter-preserving
nonlinear block projector. This is a proof of its concrete program semantics;
no step solver, progress certificate or totality oracle is assumed. -/
theorem actualUniformBlockProjection : PlainBlockSplitTargets.ActualUniformBlockProjection := by
  intro bound p hnd ha hp ν
  rw [project_meaning]
  have hmean := run_meaning bound.length [(bound, p)] (initial_good bound p hnd ha hp) ν
  refine hmean.trans ?_
  constructor
  · rintro ⟨s, hs, htruth⟩
    have he : s = (bound, p) := List.mem_singleton.mp hs
    simpa only [he] using htruth
  · intro htruth
    exact ⟨(bound, p), List.mem_singleton_self _, htruth⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof

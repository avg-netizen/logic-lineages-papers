module
public import LogicLineages.OrdinalComparison.ParametricPairWorklistExecutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Proof
open ParametricFinitePairCollapse

theorem terminal_fixed (G : Nat → Nat) (k n : Nat) : run G k ([],[n])=([],[n]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show run G (k+1) ([],[n])=step G (run G k ([],[n])) from
      Function.iterate_succ_apply' _ _ _]
    rw [ih]
    rfl

theorem result_some (s : State) (n : Nat) : result s=some n → s=([],[n]) := by
  rcases s with ⟨ts,vs⟩
  cases ts with
  | cons t ts => simp [result]
  | nil =>
    cases vs with
    | nil => simp [result]
    | cons v vs =>
      cases vs with
      | cons w ws => simp [result]
      | nil => simp [result]

theorem exactSuccess : Targets.ExactSuccess := by
  intro G p
  obtain ⟨N,hN⟩ := continuationCalibration G p [] []
  have hterm : run G N (initial p)=([],[value G p]) := hN
  have hs : ∀ fuel n, evaluate G p fuel=some n → n=value G p := by
    intro fuel n hn
    have ht := result_some _ n hn
    have hcomm : run G N (run G fuel (initial p))=run G fuel (run G N (initial p)) := by
      simp only [run,← Function.iterate_add_apply,Nat.add_comm]
    rw [ht,hterm,terminal_fixed,terminal_fixed] at hcomm
    simpa using hcomm
  have he : evaluate G p N=some (value G p) := by
    simp only [evaluate,hterm,result]
  refine ⟨hs,⟨N,he⟩,?_⟩
  have hdom : (firstFuel G p).Dom := by
    apply Nat.rfind_dom.mpr
    refine ⟨N,?_,?_⟩
    · simp [he]
    · intro m hm
      trivial
  obtain ⟨k,hk⟩ := Part.dom_iff_mem.mp hdom
  have hktrue := Nat.rfind_spec hk
  have hv : ∃ n, evaluate G p k=some n := by
    cases hv : evaluate G p k with
    | none => simp [hv] at hktrue
    | some n => exact ⟨n,rfl⟩
  obtain ⟨n,hn⟩ := hv
  have hneq := hs k n hn
  subst n
  refine ⟨k,hk,hn,?_⟩
  intro m hm
  have hf := Nat.rfind_min hk hm
  cases hv : evaluate G p m with
  | none => rfl
  | some v => simp [hv] at hf
end LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Proof

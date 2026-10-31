module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanksTargets
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanks.Proof
open CotreeGrammarFlow CotreeGrammarConnected

inductive Steps {Q : Type} (R : Q → Q → Prop) : Q → Q → Nat → Prop where
  | refl (x) : Steps R x x 0
  | tail {x y z n} : Steps R x y n → R y z → Steps R x z (n + 1)

variable {Q : Type} {R : Q → Q → Prop}

theorem steps_reach {x y n} (h : Steps R x y n) : Relation.ReflTransGen R x y := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail h

theorem reach_steps {x y} (h : Relation.ReflTransGen R x y) : ∃ n, Steps R x y n := by
  induction h with
  | refl => exact ⟨0,.refl _⟩
  | tail _ h ih =>
    rcases ih with ⟨n,hn⟩
    exact ⟨n+1,.tail hn h⟩

theorem steps_last {x y n} (h : Steps R x y n) :
    x = y ∨ ∃ p m, Steps R x p m ∧ R p y ∧ n = m + 1 := by
  cases h with
  | refl => exact Or.inl rfl
  | tail h e => exact Or.inr ⟨_,_,h,e,rfl⟩

noncomputable def distance (R : Q → Q → Prop) (x y : Q) : Nat := by
  classical
  exact if h : ∃ n, Steps R x y n then Nat.find h else 0

theorem distance_spec {x y} (h : Relation.ReflTransGen R x y) :
    Steps R x y (distance R x y) := by
  classical
  have hx := reach_steps h
  simp only [distance, dif_pos hx]
  exact Nat.find_spec hx

theorem distance_min {x y n} (h : Steps R x y n) : distance R x y ≤ n := by
  classical
  have hx : ∃ n, Steps R x y n := ⟨n,h⟩
  simp only [distance, dif_pos hx]
  exact Nat.find_min' hx h

theorem distance_root (R : Q → Q → Prop) (x : Q) : distance R x x = 0 :=
  Nat.eq_zero_of_le_zero (distance_min (.refl x))

theorem distance_predecessor {x y} (h : Relation.ReflTransGen R x y) (hne : y ≠ x) :
    ∃ p, R p y ∧ distance R x y = distance R x p + 1 := by
  rcases steps_last (distance_spec h) with he | ⟨p,m,hp,hedge,hlen⟩
  · exact (hne he.symm).elim
  · refine ⟨p,hedge,?_⟩
    have ha := distance_min hp
    have hb := distance_min (Steps.tail (distance_spec (steps_reach hp)) hedge)
    omega

variable [Fintype Q] [DecidableEq Q]

theorem edge_consumed_source (δ : Q → Q → Q) (c : Counts Q) {x y}
    (h : UsedEdge δ c x y) : 0 < consumed δ c x := by
  rcases h with ⟨r,s,hpos,he,_⟩
  have hle : c.binary (r,s) ≤ ∑ p : Q × Q, if δ p.1 p.2 = x then c.binary p else 0 := by
    calc
      _ = (if δ (r,s).1 (r,s).2 = x then c.binary (r,s) else 0) := by simp [he]
      _ ≤ _ := Finset.single_le_sum
        (f := fun p : Q × Q => if δ p.1 p.2 = x then c.binary p else 0)
        (s := Finset.univ) (a := (r,s)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (r,s))
  unfold consumed
  omega

theorem ranks_connected (δ : Q → Q → Q) (root : Q) (c : Counts Q) (rank : Q → Nat)
    (h : RankedSupport δ root c rank) : Connected δ root c := by
  have hall : ∀ n q, rank q = n → 0 < consumed δ c q →
      Relation.ReflTransGen (UsedEdge δ c) root q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q he hq
      by_cases hroot : q = root
      · subst q; exact .refl
      · rcases h.2 q hroot with ⟨hz,_⟩ | ⟨_,p,hp,hrank,hedge⟩
        · omega
        · have hpq := edge_consumed_source δ c hedge
          have hlt : rank p < n := by omega
          exact (ih (rank p) hlt p rfl hpq).tail hedge
  exact fun q hq => hall (rank q) q rfl hq

theorem connected_ranks (δ : Q → Q → Q) (root : Q) (c : Counts Q)
    (h : Connected δ root c) : ∃ rank, RankedSupport δ root c rank := by
  classical
  let R := UsedEdge δ c
  let rank : Q → Nat := fun q =>
    if q = root ∨ 0 < consumed δ c q then distance R root q + 1 else 0
  refine ⟨rank, ?_, ?_⟩
  · simp [rank, distance_root]
  · intro q hne
    by_cases hq : 0 < consumed δ c q
    · right
      rcases distance_predecessor (h q hq) hne with ⟨p,hedge,hd⟩
      have hp := edge_consumed_source δ c hedge
      have hpr : rank p = distance R root p + 1 := by simp only [rank, if_pos (Or.inr hp)]
      have hqr : rank q = distance R root q + 1 := by simp only [rank, if_pos (Or.inr hq)]
      refine ⟨hq,p,?_,?_,hedge⟩
      · omega
      · change distance R root q = distance R root p + 1 at hd
        omega
    · left
      exact ⟨by omega, by simp [rank,hne,hq]⟩

theorem rankReachabilityExact : Targets.RankReachabilityExact := by
  intro Q _ _ δ root c
  exact ⟨fun ⟨rank,h⟩ => ranks_connected δ root c rank h, connected_ranks δ root c⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanks.Proof

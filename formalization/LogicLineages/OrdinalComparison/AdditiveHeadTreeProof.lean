module
public import LogicLineages.OrdinalComparison.AdditiveHeadTreePartialProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportAssignmentProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Proof
open ActiveScalarAnnotation SourceFreeOccurrences AdmissibleAssignment AssignmentSupport

theorem curried_level_bound (n : Nat) : (Ty.curriedGround n).level ≤ 1 := by
  induction n with
  | zero => decide
  | succ n ih => change max (0+1) (Ty.curriedGround n).level ≤ 1; omega

theorem positive_index_val (n : Nat) (j : Fin ((Ty.curriedGround n).level+1))
    (hj : 0 < j.val) : j.val = 1 := by
  have := curried_level_bound n
  have := j.isLt
  omega

theorem application_trees {k Γ n} (p : AdmissibleSum.Policy)
    (F : Variable Γ (Ty.curriedGround (k+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level) (a : OrdinalVector Γ 0)
    (hq : ScalarTrees F (u 0)) (ha : ScalarTrees F (a 0))
    (hp : ∀ j, 0 < j.val → HeadTree F (u j)) :
    ScalarTrees F (application (σ := .ground) (τ := Ty.curriedGround n) p u a 0) ∧
    ∀ j, 0 < j.val → HeadTree F (application (σ := .ground) (τ := Ty.curriedGround n) p u a j) := by
  constructor
  · change ScalarTrees F (.collapse
      (ordinalBoxPositive 0 (ordinalVectorAt u) (ordinalVectorAt a) 1) (.add (u 0) (a 0)))
    have he : ordinalBoxPositive 0 (ordinalVectorAt u) (ordinalVectorAt a) 1 =
        u (UnaryCarrier.headIndex n) := by
      rw [ordinalBoxPositive]
      split
      · omega
      · have h1 : 1 < (Ty.curriedGround (n+1)).level+1 := (UnaryCarrier.headIndex n).isLt
        unfold ordinalVectorAt
        rw [dif_pos h1]
        rfl
    rw [he]
    exact .collapse (hp _ (by change 0 < 1; decide)) (.add hq ha)
  · intro j hj
    change HeadTree F (if j.val = 0 then _ else
      ordinalBoxPositive 0 (ordinalVectorAt u) (ordinalVectorAt a) j.val)
    rw [if_neg (by omega)]
    rw [ordinalBoxPositive]
    split
    · omega
    · have hlt : j.val < (Ty.curriedGround (n+1)).level+1 := by
        have := j.isLt
        change j.val < max (0+1) (Ty.curriedGround n).level+1
        omega
      unfold ordinalVectorAt
      rw [dif_pos hlt]
      exact hp _ hj

theorem abstraction_trees {k Γ m} (p : AdmissibleSum.Policy)
    (F : Variable Γ (Ty.curriedGround (k+1))) (hmlevel : m ≤ 1)
    (h : OrdinalVector (.ground :: Γ) m)
    (v : OrdinalVector Γ (max (Ty.ground.level+1) m))
    (hq : ScalarTrees (.there F) (h 0))
    (hp : ∀ i, 0 < i.val → HeadTree (.there F) (h i))
    (hv : abstraction p h = some v) :
    ScalarTrees F (v 0) ∧ ∀ j, 0 < j.val → HeadTree F (v j) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  have hs0 := groundPartialTrees k Γ F p (h 0) (ps 0) hq
    (AssignmentSupport.Proof.collect_success _ _ _ hps 0)
  have hpartial : ∀ i, HeadTree F (ps i 1) := by
    intro i
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i
      exact hs0.2
    · have hi1 : i.val = 1 := by have := i.isLt; omega
      have htree := hp i (by omega)
      have hf := actualGeneratedHeadFreeAbove Γ .ground 1 (h i) (head_grade htree) (by decide)
      have hr := AssignmentSupport.Proof.collect_success _ _ _ hps i
      rw [AdmissiblePartial.run.eq_def, if_pos hf] at hr
      have he := Option.some.inj hr
      rw [← he]
      change HeadTree F (if i.val = 1 then .add (ordinalHeadClosure (h i)) .one else .one)
      rw [if_pos hi1]
      exact .add (headClosureHead k Γ F _ htree) (head_one F)
  constructor
  · change ScalarTrees F (.add
      (repeated p .scalarRepeat (2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum)
        (ps 0 0)) (ordinalHeadClosure (h 0)))
    apply ScalarTrees.add
    · have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
        rw [List.ofFn_succ,List.map_cons,List.sum_cons]
        have := (actualTypedPartialSize Γ .ground (h 0)).1
        omega
      exact scalar_repeated p F .scalarRepeat _ _ (Nat.mul_pos (Nat.pow_pos (by omega)) hsum) hs0.1
    · exact headClosureScalar k Γ F _ hq
  · intro j hj
    have hj1 : j.val = 1 := by
      have := j.isLt
      simp only [Ty.level] at this
      omega
    have hj0 : j.val ≠ 0 := by omega
    have hj2 : j.val < Ty.ground.level+2 := by simp only [Ty.level]; omega
    have hd : HeadTree F
        (if j.val=0 then repeated p .scalarRepeat
          (2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum) (ps 0 0)
         else if hj' : j.val<Ty.ground.level+2 then
           AdmissibleSum.expand (p.shape .positiveAbstraction m) (fun i=>ps i ⟨j.val,hj'⟩)
         else ordinalHeadClosure (h ⟨j.val,by have := j.isLt;omega⟩)) := by
      rw [if_neg hj0,dif_pos hj2]
      apply head_expand
      intro i
      have he : (⟨j.val,hj2⟩ : Fin (Ty.ground.level+2)) = 1 := Fin.ext hj1
      rw [he]
      exact hpartial i
    by_cases hm : j.val < m+1
    · simpa only [dif_pos hm] using HeadTree.add hd
        (headClosureHead k Γ F _ (hp ⟨j.val,hm⟩ hj))
    · simpa only [dif_neg hm] using hd

theorem actualSourceTrees : Targets.ActualSourceTrees := by
  intro k Γ F n p e
  induction e with
  | tracked =>
    refine ⟨_,rfl,ScalarTrees.tracked,?_⟩
    intro j hj
    have he : j = UnaryCarrier.headIndex k := Fin.ext (positive_index_val _ j hj)
    rw [he]
    exact HeadTree.tracked
  | ground x =>
    refine ⟨_,rfl,ScalarTrees.free (.var x 0) ?_,?_⟩
    · intro hx
      change (⟨Ty.curriedGround (k+1),_⟩ : PackedVariable _) ∈ [⟨Ty.ground,x⟩] at hx
      have ht := congrArg Sigma.fst (List.mem_singleton.mp hx)
      simp only [Ty.curriedGround] at ht
      cases ht
    · intro j hj
      have := j.isLt
      change j.val < 0+1 at this
      omega
  | free t hf =>
    obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated _ _ p t
    have hs := AssignmentSupport.Proof.assignment_support p t u hu
    refine ⟨u,hu,ScalarTrees.free (hg 0) ?_,?_⟩
    · intro hx
      exact hf ((hs.2 _).mp hx)
    · intro j hj
      have hj1 := positive_index_val _ j hj
      refine HeadTree.free ?_ ?_
      · simpa only [hj1] using hg j
      · exact fun hx => hf (hs.1 j _ hx)
  | app f a ihf iha =>
    obtain ⟨uf,hf,hqf,hpf⟩ := ihf
    obtain ⟨ua,ha,hqa,hpa⟩ := iha
    refine ⟨application p uf ua,?_,application_trees p _ uf ua hqf hqa hpf⟩
    change (assignment p (TrackedSource.erase f)).bind (fun vf =>
      (assignment p (TrackedSource.erase a)).bind (fun va => some (application p vf va))) = _
    rw [hf]
    dsimp only [Option.bind]
    rw [ha]
  | @lam Γ F n body ih =>
    obtain ⟨h,hh,hq,hp⟩ := ih
    obtain ⟨v,hv,_⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround (n+1)) p
      (TrackedSource.erase (.lam body))
    refine ⟨v,hv,abstraction_trees p F (curried_level_bound n) h v hq hp ?_⟩
    change (assignment p (TrackedSource.erase body)).bind (fun w => abstraction p w) = some v at hv
    rw [hh] at hv
    exact hv
end LogicLineages.OrdinalComparison.Source.AdditiveHeadTree.Proof

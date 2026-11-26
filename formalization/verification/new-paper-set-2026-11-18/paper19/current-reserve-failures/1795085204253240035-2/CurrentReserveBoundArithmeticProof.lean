module
public import LogicLineages.ControlSensitivityCurrent.CurrentReservePositionalProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportStructureProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus AdmissibleSum AdmissibleAssignment
open CurrentUnaryChain (commonUnits)

private theorem copyLists {p : Policy} (xs : List (Carrier p)) (n m : Nat) :
    (List.replicate (n+m) xs).flatten =
      (List.replicate n xs).flatten ++ (List.replicate m xs).flatten := by
  rw [List.replicate_add,List.flatten_append]

theorem shapeAccount (p : Policy) (f : Nat → Nat) {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List (Carrier p)) (c : Nat)
    (hq : Account p f q xs c)
    (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q)
    {n : Nat} (s : Shape n) :
    ∃ d : Nat, Account p f (expand s (fun _ => q)) (List.replicate n xs).flatten d ∧
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (expand s (fun _ => q)) ∧
      reserve (List.replicate n xs).flatten d = (n : Int)*reserve xs c+((n : Int)-1) := by
  induction s with
  | leaf =>
    refine ⟨c,?_,ha,?_⟩
    · simpa [expand] using hq
    · simp
  | @join n m a b iha ihb =>
    obtain ⟨d,hd,hA,heA⟩ := iha
    obtain ⟨e,he, hB,heB⟩ := ihb
    have hAct : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
        (.add (expand a (fun _ => q)) (expand b (fun _ => q))) :=
      (activeAdd .here _ _).2 (Or.inl hA)
    refine ⟨d+e+1,?_,hAct,?_⟩
    · rw [copyLists]
      exact .add hAct hd he
    · rw [copyLists,reserveAdd,heA,heB]
      push_cast
      ring

theorem repeatedAccount (p : Policy) (f : Nat → Nat) {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List (Carrier p)) (c : Nat)
    (hq : Account p f q xs c)
    (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q)
    (n : Nat) (hn : 0 < n) :
    ∃ (ys : List (Carrier p)) (d : Nat),
      Account p f (repeated p .scalarRepeat n q) ys d ∧
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (repeated p .scalarRepeat n q) ∧
      reserve ys d = (n : Int)*reserve xs c+((n : Int)-1) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨d,hd,hactive,he⟩ := shapeAccount p f q xs c hq ha (p.shape .scalarRepeat n)
    exact ⟨(List.replicate (n+1) xs).flatten,d,hd,hactive,he⟩

theorem abstractionReserve (p : Policy) (f : Nat → Nat) {k Γ m}
    (h : OrdinalVector (.ground :: Ty.curriedGround (k+1) :: Γ) m)
    (v : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (max (Ty.ground.level+1) m))
    (hv : abstraction p h = some v)
    (ht : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0))
    (ha : Annotated p (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0))
    (hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0))
    (xs : List (Carrier p)) (c : Nat) (hac : Account p f (before k [] Γ (h 0)) xs c)
    (hl : 1 ≤ reserve xs c) :
    ∃ ys d, Account p f (v 0) ys d ∧ (5 : Int) ≤ reserve ys d := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  have hp := AssignmentSupport.Proof.collect_success _ _ _ hps 0
  obtain ⟨c',hc',hcc⟩ := adjacentAccountOfRun p f (h 0) ht xs c ha hac (ps 0) hp
  have hpa := (partialActive p k Γ (h 0) (ps 0) hp).2 hactive
  have hclose := adjacentCloseAccount p f k Γ (h 0) xs c hac
  let factor := 2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum
  have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
    rw [List.ofFn_succ,List.map_cons,List.sum_cons]
    have := (actualTypedPartialSize (Ty.curriedGround (k+1) :: Γ) .ground (h 0)).1
    omega
  have hfactor : 2 ≤ factor := by
    dsimp [factor,Ty.level]
    omega
  obtain ⟨ys,d,hr,har,hd⟩ := repeatedAccount p f (ps 0 0) xs c' hc' hpa factor (by omega)
  have hwhole : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
      (.add (repeated p .scalarRepeat factor (ps 0 0)) (ordinalHeadClosure (h 0))) :=
    (activeAdd .here _ _).2 (Or.inl har)
  refine ⟨ys++xs,d+c+1,.add hwhole hr hclose,?_⟩
  rw [reserveAdd,hd]
  have hpb : 1 ≤ reserve xs c' := hl.trans (reserveMonotone hcc)
  have hm := Int.mul_le_mul_of_nonneg_left hpb (show (0 : Int) ≤ (factor : Int) by omega)
  have hf : (2 : Int) ≤ (factor : Int) := by exact_mod_cast hfactor
  omega

/-- Exact generated application arithmetic. Both clauses are on Int after
the literal c/ordered carrier list construction. The nonfinite case
uses one actual non-bare active child (total child floor at least five). -/
theorem applicationBound (p : Policy) (f : Nat → Nat) {k Γ}
    (h a b : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) h)
    (hcollapse : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h (.add a b)))
    (htail : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b))
    (A B : Int) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (boundA : ∀ xs c, Account p f a xs c → A ≤ reserve xs c)
    (boundB : ∀ xs c, Account p f b xs c → B ≤ reserve xs c)
    (nonfiniteSum : Ordinal.omega0 ≤ unitValue f h → 5 ≤ A+B)
    (xs : List (Carrier p)) (c : Nat) (hac : Account p f (.collapse h (.add a b)) xs c) :
    (4 : Int) ≤ reserve xs c := by
  cases hac with
  | free hn => exact False.elim (hn hcollapse)
  | @finite _ _ xs ct n active hfinite tail =>
    have hp := unitPositive f h (AdditiveHeadTree.Proof.head_grade ht)
    rw [hfinite] at hp
    have hn : 1 ≤ n := by exact_mod_cast hp
    cases tail with
    | free hi => exact False.elim (hi htail)
    | @add _ _ xs ys ca cb _ hca hcb =>
      have ha := boundA xs ca hca
      have hb := boundB ys cb hcb
      have hl : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
      simp only [reserve,List.length_append,Nat.cast_add,Nat.cast_one] at ha hb ⊢
      omega
  | @nonfinite _ _ xs ct label _ hnonfinite _ _ tail =>
    have hsum := nonfiniteSum hnonfinite
    obtain ⟨_,_,u,hu,_,_,_,_,hvalue⟩ :=
      CurrentAffineHeads.StatementChecks.actual_head_partial_finite_surplus k Γ p f h ht
    have hδ : 1 ≤ surplus h := (hvalue (fun _ => 0) (fun _ => 0)).2.2 hnonfinite
    have hdi : (1 : Int) ≤ (surplus h : Int) := by exact_mod_cast hδ
    cases tail with
    | free hi => exact False.elim (hi htail)
    | @add _ _ xs ys ca cb _ hca hcb =>
      have ha := boundA xs ca hca
      have hb := boundB ys cb hcb
      simp only [reserve,List.length_append,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_one,Nat.cast_zero] at ha hb ⊢
      omega

end LogicLineages.ControlSensitivityCurrent.CurrentReserve

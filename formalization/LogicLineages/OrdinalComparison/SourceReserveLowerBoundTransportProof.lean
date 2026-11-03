module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundArithmeticProof
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
open ScalarCarrierAccounting ActiveScalarAnnotation AdditiveHeadTree AdmissibleAssignment

theorem account_reserve_transfer {k Γ} {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs ys : List Carrier} {c d : Nat} (hx : Account q xs c) (hy : Account q ys d) :
    reserve xs c = reserve ys d :=
  (AccountSemanticDeterminacy.Proof.accountingDeterminacy k Γ q xs ys c d hx hy).2.2.2

theorem active_add_left {k Γ} (F : Variable Γ (Ty.curriedGround (k+1)))
    (a b : OrdinalExpression Γ) (ha : Active F a) : Active F (.add a b) := by
  unfold Active at ha ⊢
  rw [AssignmentSupport.Proof.names_add]
  exact List.mem_append_left _ ha

theorem inactive_reserve {k Γ} {q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)}
    {xs : List Carrier} {c : Nat} (hn : ¬ Active (.here : Variable _ _) q)
    (hx : Account q xs c) : reserve xs c = 1 := by
  have he := account_reserve_transfer hx (Account.free hn)
  exact he

/-- The actual full vector determines the repeat count. No scalar-only size
approximation is used, and every partial coordinate remains collected. -/
theorem abstraction_reserve {k Γ m}
    (h : OrdinalVector (.ground :: Ty.curriedGround (k+1) :: Γ) m)
    (v : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (max (Ty.ground.level+1) m))
    (hv : abstraction OrdinalSyntax.defaultPolicy h = some v)
    (ht : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0))
    (ha : Annotated OrdinalSyntax.defaultPolicy
      (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0))
    (hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0))
    (xs : List Carrier) (c : Nat)
    (hac : Account (GroundPartialCarrierTransport.before k [] Γ (h 0)) xs c)
    (hl : 1 ≤ reserve xs c) :
    ∃ ys d, Account (v 0) ys d ∧ (5 : Int) ≤ reserve ys d := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  have hp := AssignmentSupport.Proof.collect_success _ _ _ hps 0
  obtain ⟨c',hc',hcc⟩ := GroundPartialCarrierTransport.Proof.adjacent_partial_account_of_run
    (h 0) ht xs c ha hac (ps 0) hp
  have hpartactive := (GroundPartialCarrierTransport.Proof.partial_active k Γ (h 0) (ps 0) hp).mpr hactive
  have hclose := GroundPartialCarrierTransport.Proof.closure_account k Γ (h 0) xs c hac
  let factor := 2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum
  have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
    rw [List.ofFn_succ,List.map_cons,List.sum_cons]
    have := (actualTypedPartialSize (Ty.curriedGround (k+1) :: Γ) Ty.ground (h 0)).1
    omega
  have hfactor : 2 ≤ factor := by
    dsimp [factor,Ty.level]
    omega
  obtain ⟨ys,d,hr,har,he⟩ := repeated_account (ps 0 0) xs c' hc' hpartactive factor (by omega)
  have hwhole := active_add_left (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
    (repeated OrdinalSyntax.defaultPolicy .scalarRepeat factor (ps 0 0)) (ordinalHeadClosure (h 0)) har
  refine ⟨ys ++ xs,d+c+1,Account.add hwhole hr hclose,?_⟩
  rw [reserve_add,he]
  have hic : (c : Int) ≤ (c' : Int) := by exact_mod_cast hcc
  have hpbound : 1 ≤ reserve xs c' := by unfold reserve at hl ⊢; omega
  have hmul := Int.mul_le_mul_of_nonneg_left hpbound (show (0 : Int) ≤ (factor : Int) by omega)
  have hfint : (2 : Int) ≤ (factor : Int) := by exact_mod_cast hfactor
  omega
end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof

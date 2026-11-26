module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveValueProof
public import LogicLineages.ControlSensitivityCurrent.CurrentSelectedCarriersStatementChecks
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open ActiveScalarAnnotation AdditiveHeadTree AdmissibleSum
open CurrentUnaryChain (commonUnits)

private theorem labelForOperator (p : Policy) (f : Nat → Nat) {k Γ}
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hOp : GroundOperatorDischarge.OperatorWitness p h) :
    ∃ a : Carrier p, LiteralOrigin (k:=k) p f h a ∧ a.head f = unitValue f h := by
  obtain ⟨r,t,u,hu,hH⟩ := hOp
  obtain ⟨u',w,v,hR⟩ := CurrentSelectedCarriers.StatementChecks.actual_operator_carriers p f
    (Ty.curriedGround (k+1) :: Γ) k r (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) t
  have he : u' = u := Option.some.inj (hR.1.symm.trans hu)
  subst u'
  refine ⟨carrierFrom hR,⟨r,t,u,w,v,hH,hR,rfl⟩,?_⟩
  have hm := hR.2.2.2.2.2.2.2 (fun _ => 0) (fun _ => 0)
  change unitValue f (v 1) = unitValue f (u (UnaryCarrier.headIndex r)) at hm
  change unitValue f (v 1) = unitValue f h
  rw [← hH]
  exact hm

theorem initialAccount (p : Policy) (f : Nat → Nat) {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (h : Annotated p (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
    ∃ (xs : List (Carrier p)) (c : Nat), SpawnedAccount p f q xs c := by
  classical
  induction h with
  | free hn => exact ⟨[],1,.free hn⟩
  | tracked => exact ⟨[],1,.tracked⟩
  | @add a b _ _ ia ib =>
    by_cases ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b)
    · obtain ⟨xs,c,hx⟩ := ia
      obtain ⟨ys,d,hy⟩ := ib
      exact ⟨xs++ys,c+d+1,.add ha hx hy⟩
    · exact ⟨[],1,.free ha⟩
  | @collapse h t hop _ _ ih =>
    by_cases ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t)
    · obtain ⟨xs,c,hx⟩ := ih
      by_cases hh : unitValue f h < Ordinal.omega0
      · obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp hh
        exact ⟨xs,c+n+HeadFiniteSurplus.surplus h,.finite ha hn hx⟩
      · obtain ⟨a,haOrigin,he⟩ := labelForOperator p f h hop
        exact ⟨xs++[a],c+HeadFiniteSurplus.surplus h,
          .nonfinite a ha (le_of_not_gt hh) he (fun _ => haOrigin) hx⟩
    · exact ⟨[],1,.free ha⟩

theorem exactAnnotatedAccounting : CurrentReserveTargets.ExactAnnotatedAccounting := by
  intro p f k Γ q ht h
  obtain ⟨xs,c,hOrigin⟩ := initialAccount p f q h
  have hAcct := forgetOrigins hOrigin
  obtain ⟨v,hv,hV⟩ := exactAccountValue p f k Γ q xs c ht hAcct
  exact ⟨xs,c,v,hOrigin,hAcct,hv,hV⟩

theorem originalCertificates (p : Policy) (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat) (e : TrackedSource.Expr k Γ F n) :
    ∃ u : OrdinalVector Γ (Ty.curriedGround n).level,
      AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
      ScalarTrees F (u 0) ∧ Annotated p F (u 0) := by
  obtain ⟨u,hu,ht,_⟩ := AdditiveHeadTree.Proof.actualSourceTrees k Γ F n p e
  obtain ⟨v,hv,ha⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k Γ F n p e
  have h := Option.some.inj (hv.symm.trans hu)
  subst v
  exact ⟨u,hu,ht,ha⟩

end LogicLineages.ControlSensitivityCurrent.CurrentReserve

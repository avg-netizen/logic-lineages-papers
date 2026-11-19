module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserveTargets

open LogicLineages.OrdinalComparison.Source
open CurrentReserve ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus
open CurrentUnaryChain (commonUnits)
open SelectedAccountPreparation (prepareSource)

/-- The actual integer accounting clauses, including a possibly negative
local delta-minus-three step. No subtraction here is interpreted in Nat. -/
def LiteralReserveRows : Prop :=
  ∀ (p : AdmissibleSum.Policy) (a : Carrier p) (xs ys : List (Carrier p)) (c d n δ : Nat),
    reserve ([] : List (Carrier p)) 1 = 1 ∧
    reserve (xs++ys) (c+d+1) = reserve xs c + reserve ys d + 1 ∧
    reserve xs (c+n+δ) = reserve xs c + (n : Int) + (δ : Int) ∧
    reserve (xs++[a]) (c+δ) = reserve xs c + (δ : Int) - 3

/-- Fresh labels are literally from the actual annotated operators, in order
and with repeats. Each successful partial is the actual selected p run. -/
def ExactAnnotatedAccounting : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
    ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q →
    Annotated p (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q →
    ∃ (xs : List (Carrier p)) (c : Nat) (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
      SpawnedAccount p f q xs c ∧ Account p f q xs c ∧
      AdmissiblePartial.run p 0 q = some v ∧
      ∀ (μ : Variable Γ .ground → Nat),
        ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (outputOne k)) =
          carrierSum f xs + (c : Ordinal)

/-- The equation is also proved for each valid structural account, including
the very same labels transported from a different original ground context. -/
def ExactAccountValue : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List (Carrier p)) (c : Nat),
    ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q →
    Account p f q xs c →
    ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
      AdmissiblePartial.run p 0 q = some v ∧
      ∀ (μ : Variable Γ .ground → Nat),
        ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (outputOne k)) =
          carrierSum f xs + (c : Ordinal)

/-- Bounds are asserted only on generated sources. The renamed form keeps
the same tracked occurrence, including occurrences beyond surrounding
ground binders in the original source. -/
def RenamedSourceFloor : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (Γ Δ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (n : Nat)
    (e : TrackedSource.Expr k Γ F n) (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (r : Renaming Γ (Ty.curriedGround (k+1) :: Δ)),
      (∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) → r F = .here →
      AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u →
      ∀ (xs : List (Carrier p)) (c : Nat), Account p f (ordinalExpressionRename r (u 0)) xs c →
        sourceFloor e ≤ reserve xs c

/-- Unconditional on actual original sources. Neither the annotation, the
head trees, successful assignment, chosen labels, partial success, nor
positive reserve is a hypothesis. Actual source representatives are cut
back to the original unrestricted grammar through the exact erasure map. -/
def ActualSourceFloor : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (left right : List Ty) (n : Nat)
    (t : OriginalTerm (left ++ Ty.curriedGround (k+1) :: right) (Ty.curriedGround n)),
    let σ := Ty.curriedGround (k+1)
    let F := SelectedBinder.selected left right σ
    @TrackedSource.Generated k (left ++ σ :: right) F n t →
    ∃ (e : TrackedSource.Expr k (left ++ σ :: right) F n)
      (u : OrdinalVector (left ++ σ :: right) (Ty.curriedGround n).level),
    let r := SelectedBinder.moveToHead left right σ
    let u' := SourceRenaming.renameVector r u
    TrackedSource.erase e = t ∧ AdmissibleAssignment.assignment p t = some u ∧
    AdmissibleAssignment.assignment p (prepareSource left right σ t) = some u' ∧
    ScalarTrees (.here : Variable (σ :: (left ++ right)) _) (u' 0) ∧
    Annotated p (.here : Variable (σ :: (left ++ right)) _) (u' 0) ∧
    ∃ (xs : List (Carrier p)) (c : Nat) (v : OrdinalPartialVector (left ++ right) σ),
      SpawnedAccount p f (u' 0) xs c ∧ Account p f (u' 0) xs c ∧
      AdmissiblePartial.run p 0 (u' 0) = some v ∧
      1 ≤ reserve xs c ∧
      (TrackedSource.active e = true → t ≠ .var F → 4 ≤ reserve xs c) ∧
      (∀ (ys : List (Carrier p)) (d : Nat),
        Account p f (u' 0) ys d → sourceFloor e ≤ reserve ys d) ∧
      ∀ (μ : Variable (left ++ right) .ground → Nat),
        ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (outputOne k)) =
          carrierSum f xs + (c : Ordinal)

/-- A map sends substituted ground names to literal zero and can only
retain/relabel typed functional names. The tracked head itself stays at
the same literal .here position under the map's lift. -/
def GroundUnitAccountTransport : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (Γ Δ : List Ty)
    (r : GroundClosing.GroundMap Γ Δ) (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (xs : List (Carrier p)) (c : Nat),
    Account p f q xs c → Account p f (GroundClosing.expression r.lift q) xs c

def ActualGroundUnitTransport : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (Γ Δ : List Ty) (n : Nat)
    (r : GroundClosing.GroundMap Γ Δ)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (xs : List (Carrier p)) (c : Nat)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (w : OrdinalPartialVector Δ (Ty.curriedGround (k+1))),
      AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
      SpawnedAccount p f (u 0) xs c ∧ Account p f (u 0) xs c ∧
      AdmissiblePartial.run p 0 (u 0) = some v ∧
      AdmissibleAssignment.assignment p (GroundCarrierTransport.close r (TrackedSource.erase e)) =
        some (GroundClosing.vector r.lift u) ∧
      Account p f (GroundClosing.expression r.lift (u 0)) xs c ∧
      AdmissiblePartial.run p 0 (GroundClosing.expression r.lift (u 0)) = some w ∧
      w = GroundClosing.partialVector r v ∧
      ∀ (μ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
        ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (outputOne k)) =
          carrierSum f xs + (c : Ordinal) ∧
        ParametricSourceSuccessor.denoteWith f (commonUnits ν) (w (outputOne k)) =
          carrierSum f xs + (c : Ordinal)

/-- Same actual carrier list and a nondecreasing integer reserve under the
actual ground scalar partial. The statement permits both .activeAdd
associations and does not require the false blanket '+2' increment. -/
def GroundPartialAccountTransport : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (left right : List Ty)
    (q : OrdinalExpression ((.ground :: left) ++ Ty.curriedGround (k+1) :: right))
    (xs : List (Carrier p)) (c : Nat),
  ScalarTrees (SelectedBinder.selected (.ground :: left) right (Ty.curriedGround (k+1))) q →
  Annotated p (SelectedBinder.selected (.ground :: left) right (Ty.curriedGround (k+1))) q →
  Account p f (before k left right q) xs c →
  ∃ (v : OrdinalPartialVector (left ++ Ty.curriedGround (k+1) :: right) .ground) (c' : Nat),
    AdmissiblePartial.run p 0 q = some v ∧
    Account p f (after k left right (v 0)) xs c' ∧ c ≤ c' ∧ reserve xs c ≤ reserve xs c'

/-- Every source instance also derives the actual sorted positional inputs,
the two successful F partials and exact original/current numeric identities.
No claim that the ground derivative itself is a source term is made. -/
def ActualGroundPartialTransport : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (k : Nat) (left right : List Ty) (n : Nat)
    (e : TrackedSource.Expr k ((.ground :: left) ++ Ty.curriedGround (k+1) :: right)
      (SelectedBinder.selected (.ground :: left) right (Ty.curriedGround (k+1))) n),
  ∃ (u : OrdinalVector ((.ground :: left) ++ Ty.curriedGround (k+1) :: right) (Ty.curriedGround n).level)
    (xs : List (Carrier p)) (c : Nat)
    (v : OrdinalPartialVector (left ++ Ty.curriedGround (k+1) :: right) .ground) (c' : Nat)
    (oldPart : OrdinalPartialVector ((.ground :: left) ++ right) (Ty.curriedGround (k+1)))
    (newPart : OrdinalPartialVector (left ++ right) (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
    AdmissibleAssignment.assignment p
      (prepareSource (.ground :: left) right (Ty.curriedGround (k+1)) (TrackedSource.erase e)) =
      some (SourceRenaming.renameVector (SelectedBinder.moveToHead (.ground :: left) right (Ty.curriedGround (k+1))) u) ∧
    SpawnedAccount p f (before k left right (u 0)) xs c ∧
    Account p f (before k left right (u 0)) xs c ∧
    AdmissiblePartial.run p 0 (u 0) = some v ∧
    Account p f (after k left right (v 0)) xs c' ∧ c ≤ c' ∧ reserve xs c ≤ reserve xs c' ∧
    AdmissiblePartial.run p 0 (before k left right (u 0)) = some oldPart ∧
    AdmissiblePartial.run p 0 (after k left right (v 0)) = some newPart ∧
    ∀ (μ : Variable ((.ground :: left) ++ right) .ground → Nat)
      (ν : Variable (left ++ right) .ground → Nat),
      ParametricSourceSuccessor.denoteWith f (commonUnits μ) (oldPart (outputOne k)) =
        carrierSum f xs + (c : Ordinal) ∧
      ParametricSourceSuccessor.denoteWith f (commonUnits ν) (newPart (outputOne k)) =
        carrierSum f xs + (c' : Ordinal)

def Full : Prop :=
  LiteralReserveRows ∧ ExactAnnotatedAccounting ∧ ExactAccountValue ∧ RenamedSourceFloor ∧
    ActualSourceFloor ∧ GroundUnitAccountTransport ∧ ActualGroundUnitTransport ∧
    GroundPartialAccountTransport ∧ ActualGroundPartialTransport

end LogicLineages.ControlSensitivityCurrent.CurrentReserveTargets

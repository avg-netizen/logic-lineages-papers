module
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Targets
open ActiveScalarAnnotation AdditiveHeadTree ScalarCarrierAccounting OriginalDomain

def CertificateRenaming : Prop := ∀ (k : Nat) (Γ Δ : List Ty)
    (r : Renaming Γ Δ) (hinj : ∀ τ : Ty, Function.Injective (fun x : Variable Γ τ => r x))
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy) (q : OrdinalExpression Γ),
  (HeadTree F q → HeadTree (r F) (ordinalExpressionRename r q)) ∧
  (ScalarTrees F q → ScalarTrees (r F) (ordinalExpressionRename r q)) ∧
  (Annotated p F q → Annotated p (r F) (ordinalExpressionRename r q))

/-- Injectivity is discharged from actual selected-permutation inverses. No
renaming or certificate correspondence is supplied as a source premise. -/
def SelectedCertificates : Prop := ∀ (k : Nat) (left right : List Ty)
    (p : AdmissibleSum.Policy) (q : OrdinalExpression (left ++ Ty.curriedGround (k+1) :: right)),
  (HeadTree (SelectedBinder.selected left right (Ty.curriedGround (k+1))) q →
    HeadTree (.here : Variable (Ty.curriedGround (k+1) :: (left ++ right)) _)
      (prepare left right (Ty.curriedGround (k+1)) q)) ∧
  (ScalarTrees (SelectedBinder.selected left right (Ty.curriedGround (k+1))) q →
    ScalarTrees (.here : Variable (Ty.curriedGround (k+1) :: (left ++ right)) _)
      (prepare left right (Ty.curriedGround (k+1)) q)) ∧
  (Annotated p (SelectedBinder.selected left right (Ty.curriedGround (k+1))) q →
    Annotated p (.here : Variable (Ty.curriedGround (k+1) :: (left ++ right)) _)
      (prepare left right (Ty.curriedGround (k+1)) q))

/-- Exact ground-prefix decomposition and actual partial naturality for every
prefix depth, not just adjacent ground/F. The original bound ground variable
stays bound during the lifted first step; only the final swap selects F. -/
def GroundPrefixStep : Prop := ∀ (left right : List Ty) (σ : Ty)
    (q : OrdinalExpression ((Ty.ground :: left) ++ σ :: right)),
  prepare (Ty.ground :: left) right σ q =
    ordinalExpressionRename (@SelectedBinder.swap (left ++ right) Ty.ground σ)
      (ordinalExpressionRename (Renaming.lift (SelectedBinder.moveToHead left right σ)) q) ∧
  ∀ (p : AdmissibleSum.Policy) (i : Nat),
    AdmissiblePartial.run p i (ordinalExpressionRename (Renaming.lift (SelectedBinder.moveToHead left right σ)) q) =
      (AdmissiblePartial.run p i q).map (SourceRenaming.renamePartial (SelectedBinder.moveToHead left right σ))

/-- Unconditional original-source/accounting preparation for ANY selected
binder position. Both complete source vectors and the actual selected scalar
partial are derived; all old shared names are moved by one actual permutation. -/
def ActualPreparedAccounting : Prop := ∀ (k : Nat) (left right : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (left ++ Ty.curriedGround (k+1) :: right)
      (SelectedBinder.selected left right (Ty.curriedGround (k+1))) n),
  ∃ (u : OrdinalVector (left ++ Ty.curriedGround (k+1) :: right) (Ty.curriedGround n).level)
    (xs : List Carrier) (c : Nat)
    (v : OrdinalPartialVector (left ++ right) (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (prepareSource left right (Ty.curriedGround (k+1)) (TrackedSource.erase e)) =
        some (SourceRenaming.renameVector (SelectedBinder.moveToHead left right (Ty.curriedGround (k+1))) u) ∧
    Account (prepare left right (Ty.curriedGround (k+1)) (u 0)) xs c ∧
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0
      (prepare left right (Ty.curriedGround (k+1)) (u 0)) = some v ∧
    ∀ μ : Variable (left ++ right) .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (v (HeadFiniteSurplus.outputOne k)) =
        carrierSum xs + (c : Ordinal)
end LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Targets

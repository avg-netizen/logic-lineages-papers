module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open CurrentGroundAccount
open CurrentReserve (Carrier SpawnedAccount Account reserve carrierSum unitValue)
open AdmissibleSum ScalarAnnotationData DeterministicAccountData
open CurrentUnaryChain (commonUnits)

def CurrentHeadClassification : Prop :=
  ∀ (f : Nat → Nat) (Γ : List Ty) (i : Nat) (q : OrdinalExpression Γ),
    GeneratedOrdinalGrade Γ i q → 0 < i →
    ∃ (normal : Nat) (finite : Bool) (value : Nat),
      UnitHeadCode.classify (OrdinalSyntax.typedCode q) = some (normal,finite,value) ∧
      (finite = true ↔ unitValue f q < Ordinal.omega0) ∧
      (finite = false ↔ Ordinal.omega0 ≤ unitValue f q) ∧
      (finite = true → (value : Ordinal) = unitValue f q)

/-- Calibration includes the literal fresh source, zero saturation, ground
closing and complete current vector, not only equality of the positive field. -/
def LiteralCarrier : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (op : Operator (Ty.curriedGround (k+1) :: Γ)),
    AdmissibleAssignment.assignment p op.source = some op.vector →
    ∃ (r : UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ))
      (w : OrdinalVector (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ) 1),
      carrierRecord p op = some r ∧
      r.source = CurrentSelectedCarriers.carrierAt (.here : Variable _ _) op.arity op.source ∧
      (∃ hA : CurrentSelectedCarriers.Realization p f (.here : Variable _ _)
        op.arity op.source op.vector w r.vector, Matches r (CurrentReserve.carrierFrom hA)) ∧
      carrierCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        (SourceAnnotationCode.operatorCode op) = some (recordCode r)

def ActualAccount : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here),
    CurrentGroundAnnotation.Valid p d →
    ∃ (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
      (xs : List (Carrier p)) (c : Nat),
      accountData p d = some (rs,c) ∧ List.Forall₂ Matches rs xs ∧
      SpawnedAccount p f (erase d) xs c ∧ Account p f (erase d) xs c ∧
      accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        (SourceAnnotationCode.code d) = some (rs.map recordCode,c)

/-- Unconditional actual original-source compiler, ordered real labels, and
the actual first field of the F partial, with the integer source floor. -/
def SourceAccount : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty) (n : Nat)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
    ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
      (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
      (xs : List (Carrier p)) (c : Nat) (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
    sourceData p P = some (u,rs,c) ∧
    sourceCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm (TrackedSource.erase P)) = some (OrdinalSyntax.vectorCode u,rs.map recordCode,c) ∧
    AdmissibleAssignment.assignment p (TrackedSource.erase P) = some u ∧
    List.Forall₂ Matches rs xs ∧ SpawnedAccount p f (u 0) xs c ∧ Account p f (u 0) xs c ∧
    CurrentReserve.sourceFloor P ≤ reserve xs c ∧ AdmissiblePartial.run p 0 (u 0) = some v ∧
    ∀ μ : Variable Γ .ground → Nat,
      ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v (HeadFiniteSurplus.outputOne k)) =
        carrierSum f xs + (c : Ordinal)

def AlgorithmsEffective : Prop :=
  ∀ p : Policy, PolicyShape.Effective p →
    Computable (fun z : List Nat × Nat => carrierCode p z.1 z.2) ∧
    Computable (fun z : List Nat × Nat => accountCode p z.1 z.2) ∧
    Computable (fun z : List Nat × Nat => sourceCode p z.1 z.2)

def Full : Prop :=
  CurrentHeadClassification ∧ LiteralCarrier ∧ ActualAccount ∧ SourceAccount ∧ AlgorithmsEffective

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountTargets

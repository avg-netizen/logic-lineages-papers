module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitRawDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnitTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence CurrentOneUnit

/-- The actual literal p-specific trees and structural sizes, not a
reassociated value substituted before taking the partial. -/
def LiteralInflation : Prop :=
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (σ τ : Ty)
    (a : OriginalTerm (σ :: Γ) τ),
    ∃ (h : OrdinalVector (σ :: Γ) τ.level)
      (h' : OrdinalVector (σ :: Γ) (Ty.arrow .ground τ).level) (d : Coefficients),
      AdmissibleAssignment.assignment p a = some h ∧
      AdmissibleAssignment.assignment p (OneUnit.unused a) = some h' ∧
      typedCoefficients p a = some d ∧ d = (OneUnit.multiplier h,OneUnit.multiplier h',ordinalHeadFree (h 0)) ∧
      0 < d.1 ∧ h' 0 = inflated p τ (h 0) ∧
      (d.2.2 = false →
        ordinalPartialSize (h' 0) =
          OneUnit.coefficient τ * ordinalPartialSize (h 0) + 3 * OneUnit.copies τ ∧
        (∀ j : Fin (τ.level+1), 0 < j.val →
          ordinalPartialSize (h j) ≤
            ordinalPartialSize (h' ⟨j.val, by have := j.isLt; simp only [Ty.level]; omega⟩)) ∧
        d.1 < d.2.1)

/-- Actual scalar observations with shared original wires; the literal
partial equations are required at the very same p and f. -/
def ActualScalarRows : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (σ τ : Ty)
    (a : OriginalTerm (σ :: Γ) τ) (d : Coefficients),
    typedCoefficients p a = some d →
    ∃ (h : OrdinalVector (σ :: Γ) τ.level)
      (h' : OrdinalVector (σ :: Γ) (Ty.arrow .ground τ).level)
      (v v' : OrdinalPartialVector Γ σ),
      AdmissibleAssignment.assignment p a = some h ∧
      AdmissibleAssignment.assignment p (OneUnit.unused a) = some h' ∧
      AdmissiblePartial.run p 0 (h 0) = some v ∧
      AdmissiblePartial.run p 0 (h' 0) = some v' ∧
      ∀ (ρ : Variable Γ .ground → Nat), ∃ P R P' R' L L' : Nat,
        0 < P ∧ 0 < R ∧ 0 < P' ∧ 0 < R' ∧ 0 < L ∧ 0 < L' ∧
        ParametricSourceSuccessor.denoteWith f (CurrentUnaryChain.commonUnits ρ) (v 0) = (P : Ordinal) ∧
        ParametricSourceSuccessor.denoteWith f (CurrentUnaryChain.commonUnits ρ) (v' 0) = (P' : Ordinal) ∧
        CurrentAbsolute.Scalar p f (headUnitWires ρ) a R ∧
        CurrentAbsolute.Scalar p f (headUnitWires ρ) (OneUnit.unused a) R' ∧
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.first a) L ∧
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.second a) L' ∧
        L = d.1*P+R ∧ L' = d.2.1*P'+R' ∧
        (d.2.2 = true → P = R+1 ∧ L = (d.1+1)*R+d.1) ∧
        (d.2.2 = false →
          P' = OneUnit.coefficient τ*P+4*OneUnit.copies τ ∧
          R' = OneUnit.coefficient τ*R+OneUnit.copies τ ∧
          L' = OneUnit.coefficient τ*d.2.1*P+OneUnit.coefficient τ*R+4*OneUnit.copies τ*d.2.1+OneUnit.copies τ)

def ExactHeadGraph : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (σ τ : Ty)
    (a : OriginalTerm (σ :: Γ) τ), 0 < σ.level →
    ∃ d : Coefficients, typedCoefficients p a = some d ∧
      0 < (equation τ.level d).1 ∧ 0 < (equation τ.level d).2.2.2.1 ∧
      (d.2.2 = false → 0 < (equation τ.level d).2.2.1) ∧
      ∀ (ρ : Variable Γ .ground → Nat) (r : Nat),
        Formula p f ρ a d r ↔ CurrentAbsolute.Scalar p f (headUnitWires ρ) a r

def ExactSelectedGraph : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (left right : List Ty) (σ τ : Ty)
    (a : OriginalTerm (left ++ σ :: right) τ), 0 < σ.level →
    let b := a.rename (SelectedBinder.moveToHead left right σ)
    ∃ d : Coefficients, typedCoefficients p b = some d ∧
      0 < (equation τ.level d).1 ∧ 0 < (equation τ.level d).2.2.2.1 ∧
      (d.2.2 = false → 0 < (equation τ.level d).2.2.1) ∧
      ∀ (ρ : Variable (left ++ σ :: right) .ground → Nat) (r : Nat),
        Formula p f (UnitObservation.remainingInputs left right σ ρ) b d r ↔
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) a r

def ExactMoveCodes : Prop :=
  ∀ (left right : List Ty) (σ τ : Ty) (a : Input (left ++ σ :: right) τ),
    moveCode left.length (RawSourceDAG.encode ⟨left ++ σ :: right,τ,a⟩) =
      some (RawSourceDAG.encode ⟨σ :: left ++ right,τ,
        ScopedDAG.renameInput (SelectedBinder.moveToHead left right σ) a⟩)

def ExactHeadCodes : Prop :=
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (σ τ : Ty) (a : OriginalTerm (σ :: Γ) τ)
    (d : Coefficients), 0 < σ.level → typedCoefficients p a = some d →
    compileHead p ((σ :: Γ).map SyntaxCode.typeCode,SyntaxCode.encodeTerm a) =
      some (literalPacket a d)

def ExactSelectedCodes : Prop :=
  ∀ (p : AdmissibleSum.Policy) (left right : List Ty) (σ τ : Ty)
    (a : OriginalTerm (left ++ σ :: right) τ) (d : Coefficients),
    let b := a.rename (SelectedBinder.moveToHead left right σ)
    0 < σ.level → typedCoefficients p b = some d →
    compileSelected p (left.length,(left ++ σ :: right).map SyntaxCode.typeCode,SyntaxCode.encodeTerm a) =
      some (literalPacket b d)

def Effective : Prop :=
  Primrec₂ equation ∧
  ∀ (p : AdmissibleSum.Policy), PolicyShape.Effective p →
    Computable (compileHead p) ∧ Computable (compileSelected p)

def Full : Prop :=
  LiteralInflation ∧ ActualScalarRows ∧ ExactHeadGraph ∧ ExactSelectedGraph ∧
    ExactMoveCodes ∧ ExactHeadCodes ∧ ExactSelectedCodes ∧ Effective

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnitTargets

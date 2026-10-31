module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionDefinitions
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector
open OriginalDomain
abbrev unary : Ty := .arrow .ground .ground

def groundExtension {Γ} (ρ : AdmissibleSubstitution Γ) (n : Nat) :
    AdmissibleSubstitution (.ground::Γ) where
  vector := fun {_} x j => match x with
    | .here => UnitObservation.positive n
    | .there y => ρ.vector y j
  graded := by
    intro σ x j
    cases x with
    | here =>
      have hj : j=0 := Fin.eq_zero j
      subst j
      exact UnitObservation.positiveGrade n
    | there y => exact ρ.graded y j
  bounded := by
    intro σ x j
    cases x with
    | here => exact le_rfl
    | there y => exact ρ.bounded y j

def extend {Γ} (ρ : AdmissibleSubstitution Γ) (z w : Nat) :=
  groundExtension (groundExtension ρ w) z

def shiftTwo (Γ : List Ty) : Renaming Γ (.ground::.ground::Γ) :=
  fun {_} x => .there (.there x)

def pad {Γ} (a : OriginalTerm Γ unary) (z : OriginalTerm Γ .ground) :
    OriginalTerm Γ unary := .app (.lam (a.rename (Renaming.weaken Γ .ground))) z

def alignedLeft {Γ} (a : OriginalTerm Γ unary) :
    OriginalTerm (.ground::.ground::Γ) unary := pad (a.rename (shiftTwo Γ)) (.var .here)
def alignedRight {Γ} (b : OriginalTerm Γ unary) :
    OriginalTerm (.ground::.ground::Γ) unary := pad (b.rename (shiftTwo Γ)) (.var (.there .here))

/-- Both unused binders are fresh and lifted capture-avoidantly under all
internal binders. This is the literal manuscript S, not an ordinal primitive. -/
def combine {Γ} (a b : OriginalTerm Γ unary) : OriginalTerm Γ unary :=
  .app (.lam (a.rename (Renaming.weaken Γ (.arrow .ground unary))))
    (.lam (b.rename (Renaming.weaken Γ .ground)))

def payload {Γ} (a b : OriginalTerm Γ unary) : OriginalTerm Γ .ground :=
  .app (combine b a) (.app (combine a b)
    (.app (combine b b) (.app (combine a a) .zeroC)))
def left {Γ} (a b : OriginalTerm Γ unary) : OriginalTerm Γ .ground :=
  SourceCollisionCompletion.eraser (.app (combine a a) (payload a b))
    (.app (combine b b) (payload a b))
def right {Γ} (a b : OriginalTerm Γ unary) : OriginalTerm Γ .ground :=
  SourceCollisionCompletion.eraser (.app (combine a b) (payload a b))
    (.app (combine b a) (payload a b))

def HeadEqual {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) : Prop :=
  ∃ av bv : OrdinalVector Γ 1,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some bv ∧
    expressionValue ρ (av 1)=expressionValue ρ (bv 1)
def VectorEqual {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) : Prop :=
  ∃ av bv : OrdinalVector Γ 1,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some bv ∧
    ∀ j : Fin 2, expressionValue ρ (av j)=expressionValue ρ (bv j)
def Detects {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) : Prop :=
  let l := SourceCollisionCompletion.rawScalar (valuation ρ) (left a b)
  let r := SourceCollisionCompletion.rawScalar (valuation ρ) (right a b)
  r≤l ∧ (l=r ↔ VectorEqual ρ a b) ∧ (¬VectorEqual ρ a b → r+2≤l)
end LogicLineages.OrdinalComparison.Source.FunctionalDetector

module
public import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversal
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedCircuitSequential (Gate Topological)
open OriginalPrintedCircuitTerminal (observe)
open OriginalPrintedTypedExistential (HasSuccessfulObservation solveOriginal)

/-- An original baseline is in the domain exactly when the actual
original observer returns one of its two successful Boolean statuses. -/
def Defined (f base : Nat → Nat) (gates : List Gate) (p : NormalForm.Formula) : Prop :=
  ∃ b : Bool, observe f base gates (.rows p) = .ok b

def Total (f : Nat → Nat) (gates : List Gate) (p : NormalForm.Formula) : Prop :=
  ∀ base : Nat → Nat, Defined f base gates p

def HoldsOnDomain (f : Nat → Nat) (gates : List Gate) (p : NormalForm.Formula)
    (polarity : Bool) : Prop :=
  ∀ base : Nat → Nat, Defined f base gates p → observe f base gates (.rows p) = .ok polarity

/-- Absence of a genuinely successful contrary observation. Errors
never stand for false observations or witnesses of a quantified test. -/
noncomputable def solveUniversal (f : Nat → Nat) (B : Nat) (known : List Nat)
    (gates : List Gate) (p : NormalForm.Formula) (polarity : Bool) : Bool :=
  !(solveOriginal f B known gates p (!polarity))

def ExactDefinedDomainCounterexample : Prop :=
  ∀ (f : Nat → Nat) (gates : List Gate) (p : NormalForm.Formula) (polarity : Bool),
    (¬ HasSuccessfulObservation f gates p (!polarity)) ↔ HoldsOnDomain f gates p polarity

def ExactOriginalTypedDomainUniversal : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      Topological known gates → PlainPreparedFormula p → ∀ polarity : Bool,
        (solveUniversal f B known gates p polarity = true ↔ HoldsOnDomain f gates p polarity) ∧
        (solveUniversal f B known gates p polarity = false ↔ HasSuccessfulObservation f gates p (!polarity))

def ExactOriginalTypedTotalUniversal : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      Topological known gates → PlainPreparedFormula p →
      Total f gates p → ∀ polarity : Bool,
        (solveUniversal f B known gates p polarity = true ↔
          ∀ base : Nat → Nat, observe f base gates (.rows p) = .ok polarity)

def FullOriginalPrintedTypedDomainUniversal : Prop :=
  ExactDefinedDomainCounterexample ∧ ExactOriginalTypedDomainUniversal ∧ ExactOriginalTypedTotalUniversal

end LogicLineages.PermittedControl.OriginalPrintedTypedDomainUniversal

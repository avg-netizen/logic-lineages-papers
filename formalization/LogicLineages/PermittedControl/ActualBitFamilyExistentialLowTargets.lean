module
public import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesTargets
public import LogicLineages.PermittedControl.OriginalPrintedZeroSupportTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates dimension originalRows wantedBits strips)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalPrintedZeroSupport (closedSnapshot)

def closedClause (clause : List BitRow) : Bool :=
  match closedSnapshot (originalRows clause) with
  | none => false
  | some values => decide (values.map Prod.snd = wantedBits clause)

def closed (family : Family) : Bool := family.any closedClause

noncomputable def children (f : Nat → Nat) (bound : Nat) (family : Family) : List Family :=
  (coordinates family).toList.flatMap (fun name => (strips f name bound family).map Prod.snd)

def Satisfiable (f : Nat → Nat) (family : Family) : Prop := ∃ ρ : Nat → Nat, Holds f ρ family

def ExactBitFamilySupportLocality : Prop :=
  ∀ (f ρ σ : Nat → Nat) (family : Family), (∀ k ∈ coordinates family, ρ k = σ k) →
    (Holds f ρ family ↔ Holds f σ family)

def ExactBitFamilyClosed : Prop :=
  ∀ (f : Nat → Nat) (family : Family), dimension family = 0 →
    (closed family = true ↔ Satisfiable f family)

def ExactBitFamilyExistentialLow : Prop :=
  ∀ (f : Nat → Nat) (bound : Nat) (family : Family),
    ((∃ ρ : Nat → Nat, (∃ name ∈ coordinates family, ρ name < bound) ∧ Holds f ρ family) ↔
      ∃ out ∈ children f bound family, Satisfiable f out)

def ExactBitFamilyExistentialLowDimension : Prop :=
  ∀ (f : Nat → Nat) (bound : Nat) (family : Family), ∀ out ∈ children f bound family,
    dimension out < dimension family

def FullActualBitFamilyExistentialLow : Prop :=
  ExactBitFamilySupportLocality ∧ ExactBitFamilyClosed ∧ ExactBitFamilyExistentialLow ∧
    ExactBitFamilyExistentialLowDimension

end LogicLineages.PermittedControl.ActualBitFamilyExistentialLow

module
public import LogicLineages.PermittedControl.OriginalMatrixUniformHighBoundTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranchesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixActualHighPacket
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open ActualFiniteOrderBranches (Pattern realized guard)
open OriginalPrintedPlainMatrixInfiniteLow (circuit)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalMatrixPaidOrderRow (IsOrder stateAfterShort)
open ActualReadChargeIteration (ReadState Trace stateCharge stateValue RankBound)
open ActualPaidTerminalSignNormalization (SignedTerminal)
open ActualZeroClassReplacement (liftedReads)
open OriginalMatrixActualReadTape (readState)
open OriginalMatrixPaidCongruence (enabledRows rankLayout)
open OriginalMatrixUniformHighBound (Funds ceiling)
open OriginalNormalizedCircuitMatrix (passingList)

def OrderTerminal (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r z : Nat)
    (row : Row) (v : Int) (bit : Bool) : Prop :=
  ∃ (source : ReadState) (n : Nat) (final : ReadState),
    readState f ρ row = some source ∧ stateValue source = v ∧
    Trace f B ρ r z n (stateAfterShort source) final ∧
    n ≤ stateCharge r (stateAfterShort source) ∧ SignedTerminal f ρ z final ∧
    liftedReads f ρ final.reads ∧ RankBound r z final ∧
    (∀ rd ∈ final.reads, ∃ t ∈ row.2.2, rd.1.2.rank = t.2.rank) ∧
    stateValue final = v ∧ row.1.atPolarity bit (stateValue final)

/-- Original index/order alignment: no sorting, erasure, separate field
valuations, or pulling an order trace from some other row. -/
def OrderedTraces (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r z : Nat) :
    List Row → Snapshot → Prop
  | [], [] => True
  | row :: rs, (v,bit) :: vs =>
      (IsOrder row.1 → OrderTerminal f B ρ r z row v bit) ∧ OrderedTraces f B ρ r z rs vs
  | _, _ => False

def Packet (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r z : Nat) (rs : List Row)
    (values : Snapshot) : Prop :=
  enabledRows f ρ (rankLayout rs) rs values ∧ OrderedTraces f B ρ r z rs values

def ExactActualHighPacket : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r z : Nat) (rs : List Row),
    (∀ row ∈ rs, ∀ t ∈ row.2.2, t.2.rank < r ∧ t.2.rank ≤ z) →
    (∀ row ∈ rs, Funds B r z ρ row) →
    ∀ values : Snapshot, actualRows f ρ rs values ↔ Packet f B ρ r z rs values

noncomputable def originalBranchCeiling (B : Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) : Nat :=
  ceiling B branch.1 (renamed known gates p branch)

noncomputable def originalFamilyCeiling (B : Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) : Nat :=
  (branches known gates p).foldr (fun branch n => max (originalBranchCeiling B known gates p branch) n) 0

def ExactOriginalFamilyHighBound : Prop :=
  ∀ (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern), branch ∈ branches known gates p →
      originalBranchCeiling B known gates p branch ≤ originalFamilyCeiling B known gates p

def BranchPacket (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (polarity : Bool) (branch : Pattern) : Prop :=
  ∃ suffix : Snapshot,
    Packet f B (realized θ branch) branch.1 (branch.1-1) (renamed known gates p branch)
      (passingList θ (circuit known gates p) ++ suffix) ∧
      OriginalPlainTerminalMatrix.accepts p polarity suffix

/-- The *same* actual initial branch and value assignment, retaining
the original linear branch guard and the inherited prior. This is
pointwise conditional on payment, not a symbolic continuation theorem. -/
def ExactOriginalPaidBranchPacket : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (polarity : Bool) (branch : Pattern),
      branch ∈ branches known gates p →
      originalFamilyCeiling B known gates p ≤ realized θ branch 0 →
        ((guard branch).eval θ ∧ prior θ ∧ SourceAccepts f θ known gates p polarity) ↔
        (guard branch).eval θ ∧ prior θ ∧ BranchPacket f B θ known gates p polarity branch

def FullOriginalMatrixActualHighPacket : Prop :=
  ExactActualHighPacket ∧ ExactOriginalFamilyHighBound ∧ ExactOriginalPaidBranchPacket

end LogicLineages.PermittedControl.OriginalMatrixActualHighPacket

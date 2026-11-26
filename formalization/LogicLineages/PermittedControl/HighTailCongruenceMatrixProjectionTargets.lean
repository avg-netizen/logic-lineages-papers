module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
public import LogicLineages.PermittedControl.HighTailNamedRowProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection
open OrdinalComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedSameRankResidue (properOperand)
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow commonLayout requests)
open SignedCongruenceMatrix (formula compileCode commonTail commonTailCode actualRows)
open HighTailNamedRowProjection (lowerGuard lowerGuardCode)

abbrev Args := Nat × Nat × List RawArgs

noncomputable def guarded (B name : Nat) (rows : List SourceRow) : NormalForm.Formula :=
  .conjunction (lowerGuard name (commonTail B rows)) (formula rows)

noncomputable def projected (B name : Nat) (rows : List SourceRow) : NormalForm.Formula :=
  LinearRows.eliminate name (guarded B name rows)

/-- Add the one actual common tail guard and eliminate the selected name
once from the entire simultaneous conjunction. Keep the shared tape. -/
def projectCode (p : Args) : Option (List NamedCode × Nat) :=
  let (B,name,rows) := p
  (compileCode rows).map (fun packet =>
    (packet.1,LinearRows.Code.eliminate name (6 * Nat.pair (lowerGuardCode name (commonTailCode B rows)) packet.2 + 4)))

def CodeExact : Prop :=
  Primrec projectCode ∧
  (∀ (B name : Nat) (rows : List RawArgs), projectCode (B,name,rows) = none ↔ ∃ r ∈ rows, r.1 = 0) ∧
  ∀ (B name : Nat) (rows : List SourceRow), (∀ r ∈ rows, 0 < r.1) →
    projectCode (B,name,rows.map encodeRow) =
      some ((requests (commonLayout rows)).map encodeRequest,(projected B name rows).encode)

def OutputSupport : Prop :=
  ∀ (B name : Nat) (rows : List SourceRow),
    LinearRows.isLinear name (guarded B name rows) = true ∧
    ∀ i : Nat, i ∈ (projected B name rows).variables ↔ i ≠ name ∧ i ∈ (formula rows).variables

def ActualJointProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (name rank : Nat) (rows : List SourceRow) (ρ ν : Nat → Nat),
    (name,rank) ∈ commonLayout rows →
    (∀ r ∈ rows, 0 < r.1 ∧ ∀ t ∈ r.2.2, properOperand t.2) →
    (∀ k ∈ (commonLayout rows).map Prod.snd, k ≠ rank → commonTail B rows ≤ ρ k) →
    (∀ s ∈ commonLayout rows, s.1 ≠ name → ν s.1 = ρ s.2) →
    ((projected B name rows).eval ν ↔
      ∃ z : Nat, commonTail B rows ≤ z ∧
        ∃ values : List (List Nat), actualRows f (Function.update ρ rank z) rows values)

def FullHighTailCongruenceMatrixProjection : Prop := CodeExact ∧ OutputSupport ∧ ActualJointProjection

end LogicLineages.PermittedControl.HighTailCongruenceMatrixProjection

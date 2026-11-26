module
public import LogicLineages.PermittedControl.HighFieldPreparedPacketTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

def FullCompilerEffective : Prop := Primrec compile

/-- Exact original high comparison at a chosen strict order of the
two ranks (equal ranks may be used twice). The compiled lower requests
are paid by their actual reads at that same original valuation. -/
def ActualPreparedComparison : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (F G : ValueField), ProperField F → ProperField G →
  ∀ (ρ : Nat → Nat), StrictMono ρ → ∀ (rankF rankG wanted : Nat),
    highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤
        min (ρ rankF) (ρ rankG) →
    ∃ (vF vG : Nat) (table : List LowerOperand) (p : NormalForm.Formula),
      FieldValue f F (ρ rankF) vF ∧ FieldValue f G (ρ rankG) vG ∧
      (∀ u v : Nat, FieldValue f F (ρ rankF) u → FieldValue f G (ρ rankG) v → u = vF ∧ v = vG) ∧
      compile (longFieldCode F,longFieldCode G,rankF,rankG,wanted) = preparedPacketCode table p ∧
      PreparedInput table p ∧ table.length ≤ 1 ∧
      (∀ op ∈ table, ∃ H : ValueField, op = .ordinary (min rankF rankG) H) ∧
      (∃ ν : Nat → Nat,
        ν 0 = ρ (max rankF rankG) ∧ PreparedTableTied f (max rankF rankG) ρ table ν ∧
        ∀ (j : Nat) (used : j < table.length),
          lowerOperandRead f ρ (table.get ⟨j,used⟩) = some (some (ν (j+1)))) ∧
      (∀ ν : Nat → Nat, ν 0 = ρ (max rankF rankG) →
        PreparedTableTied f (max rankF rankG) ρ table ν →
        (p.eval ν ↔ numericalComparison vF vG = wanted))

def FullHighFieldPreparedComparison : Prop := FullCompilerEffective ∧ ActualPreparedComparison

end LogicLineages.PermittedControl.HighFieldPreparedPacket

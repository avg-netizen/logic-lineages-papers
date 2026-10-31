module
public import LogicLineages.OrdinalComparison.WWUnitObservationTargets
public import LogicLineages.OrdinalComparison.WWSelectedBinderStatementChecks
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitObservation.Proof
open OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem positiveValue : Targets.PositiveValue := by
  intro n
  induction n with
  | zero => simp [positive,closedValue,denote]
  | succ n ih =>
      change ordinalNaturalSum (closedValue (positive n)) 1 = (((n+1)+1 : Nat) : Ordinal)
      rw [ih]
      simpa only [Nat.cast_one] using naturalSum_finite (n+1) 1

theorem groundValue : Targets.GroundValue := by
  intro Γ ρ x
  exact ⟨rfl,positiveValue (ρ x)⟩

theorem functionalCoordinates : Targets.FunctionalCoordinates := by
  intro Γ ρ σ hs x j
  cases σ with
  | ground => simp [Ty.level] at hs
  | arrow a b => rfl

theorem selectedTransport : Targets.SelectedTransport := by
  intro left right σ hs ρ τ x j
  have hx := (SelectedBinder.StatementChecks.inverses left right σ τ).1 x
  cases τ with
  | ground =>
      cases he : SelectedBinder.moveToHead left right σ x with
      | here => simp [Ty.level] at hs
      | there y =>
          rw [he] at hx
          simpa only [OneUnit.unitExtension,substitution,vector,remainingInputs,he] using
            congrArg (fun z => positive (ρ z)) hx
  | arrow a b =>
      cases he : SelectedBinder.moveToHead left right σ x with
      | here => simp [OneUnit.unitExtension,substitution,vector,he]
      | there y => simp [OneUnit.unitExtension,substitution,vector,he]

theorem selectedValuation : Targets.SelectedValuation := by
  intro left right σ hs ρ
  funext c
  rcases c with ⟨τ,x,j⟩
  change closedValue ((OneUnit.unitExtension (σ := σ)
      (substitution (remainingInputs left right σ ρ))).vector
      (SelectedBinder.moveToHead left right σ x) j) =
    closedValue ((substitution ρ).vector x j)
  rw [selectedTransport left right σ hs ρ τ x j]
end LogicLineages.OrdinalComparison.Source.UnitObservation.Proof

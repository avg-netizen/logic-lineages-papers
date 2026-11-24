module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit CountFit)
open NumberedWindowInternalDirectCoreReinstallTargets (Reinstalled)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit)
open NumberedWindowInternalDirectTypedListTargets (jRaw Reports)

def ExactReinstallTypedList : Prop :=
  ∀ (xs : Entries) (s : Settings) (i : Program 1) (r : Program 3) (count : Program 2),
    ScalarFit i (checks xs s).scalar → PositiveFit r (checks xs s).positive →
    CountFit count → Reinstalled xs s i (jRaw i) r count

def ExactSelectedReinstallTypedList : Prop :=
  ∀ (xs : Entries) (s : Settings) (count : Program 2), CountFit count →
    ∃ (i : Program 1) (r : Program 3), Reinstalled xs s i (jRaw i) r count

/-- The literal odd carrier of exactly this new body, not the old carrier,
chooses the genuine selected parser payload and typed scratch. -/
def ExactInstalledTypedCarrier : Prop :=
  ∀ (i : Program 1) (r : Program 3) (count : Program 2) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw : OTerm α) (goal : Formula α),
    let S := data i (jRaw i) r (dCore i r count)
    let B := sourceBody S c
    Nonempty (Derivation B Γ (carrier S true c raw)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (decoded : OTerm β),
      (∀ p ∈ Γ, p.relabel ρ ∈ Δ) → Reports i B Δ (raw.relabel ρ) decoded →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

def ExactIntroInstalledTypedCarrier : Prop :=
  ∀ (i : Program 1) (r : Program 3) (count : Program 2) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw decoded : OTerm α),
    let S := data i (jRaw i) r (dCore i r count)
    let B := sourceBody S c
    Reports i B Γ raw decoded → Nonempty (Derivation B Γ (carrier S true c raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListInstallTargets

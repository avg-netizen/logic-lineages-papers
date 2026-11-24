module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTapeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (certificate)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (reports tripleTerm)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

/-- The original odd certificate in the freshly chosen body supplies the
same directed raw [source,witness,target] acceptance and shared reports.
This object elimination needs no numerical fit for the chosen observer. -/
def ExactInstalledCertificateSharedTape : Prop :=
  ∀ (i j : Program 1) (r : Program 3) (count : Program 2) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (src w dst : OTerm α) (goal : Formula α),
    let S := data i j r (dCore i r count)
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S true c src dst w)) →
    (∀ (β : Type) (ρ : α → β) (Δ : List (Formula β))
        (kept removed inserted s t k d a p sk tp : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      Nonempty (Derivation B Δ (reports 5 (w.relabel ρ) kept removed inserted)) →
      Nonempty (Derivation B Δ (equal (w.relabel ρ) (tripleTerm 5 kept removed inserted))) →
      Nonempty (Derivation B Δ (programGraph (boundaryRaw i) (suc z)
        (sourceTape (src.relabel ρ) (dst.relabel ρ) removed))) →
      Reports count count r B Δ (src.relabel ρ) (dst.relabel ρ)
        kept removed inserted s t k d a p sk tp →
      Nonempty (Derivation B Δ (goal.relabel ρ))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreInstalledCertificateTargets

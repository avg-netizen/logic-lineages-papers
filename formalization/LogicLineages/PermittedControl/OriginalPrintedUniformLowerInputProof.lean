module
public import LogicLineages.PermittedControl.OriginalPrintedUniformLowerInputTargets
import LogicLineages.PermittedControl.ActualRankChartPrototypeProof
import LogicLineages.PermittedControl.OriginalPrintedUniformHighResidualProof
import LogicLineages.PermittedControl.OriginalPrintedUniformHighResidualTransportProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsContextProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedUniformLowerInput
open ActualRankChartPrototype (prototype exactOriginalChartPrototype)
open ActualLowerRankChartRows (lowerChart exactLowerRankChartRows)
open ActualBoundedSignedRouteSemantics (tiedBelow)
open ActualSelectedSignedRouteProjection (LowerHolds project)
open ActualPreparedSlotAppend (Packet)
open ActualGreatestRouteResidual (lowerFamily LowerMatrix Residual exactActualLowerRouteFamily)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedUniformHighResidual (outcomes candidates candidateShape exactOriginalPrintedUniformHighResidual)
open OriginalPrintedHighResidual (GuardedAccepts)
open ActualFiniteOrderBranches (realized)
open OriginalPrintedRankedLiteralHigh (chartMinimum cutoff)

private theorem tiedTruth (f ρ σ : Nat → Nat) (top : Nat) (agr : ∀ i < top, ρ i = σ i)
    (p : Packet) : LowerHolds f ρ top p ↔ LowerHolds f σ top p := by
  constructor
  · rintro ⟨ν,fit,holds⟩
    exact ⟨ν,(tiedBelow f ρ σ top p.1 ν agr).mp fit,holds⟩
  · rintro ⟨ν,fit,holds⟩
    exact ⟨ν,(tiedBelow f ρ σ top p.1 ν agr).mpr fit,holds⟩

private theorem familyTruth (f ρ σ : Nat → Nat) (top bound : Nat) (qs : List Packet)
    (safe : ∀ q ∈ qs, ActualSelectedSignedRoutePacket.Shape q) (agr : ∀ i < top, ρ i = σ i) :
    (∃ out ∈ lowerFamily top bound qs, LowerMatrix f ρ out) ↔
      ∃ out ∈ lowerFamily top bound qs, LowerMatrix f σ out := by
  have left := (exactActualLowerRouteFamily f ρ top bound qs safe).2
  have right := (exactActualLowerRouteFamily f σ top bound qs safe).2
  refine left.symm.trans (Iff.trans ?_ right)
  constructor
  · rintro ⟨q,used,truth⟩
    exact ⟨q,used,(tiedTruth f ρ σ top agr (project bound q)).mp truth⟩
  · rintro ⟨q,used,truth⟩
    exact ⟨q,used,(tiedTruth f ρ σ top agr (project bound q)).mpr truth⟩

theorem exactOriginalPrintedUniformLowerInput : ExactOriginalPrintedUniformLowerInput := by
  intro f B selected known gates p plain positive branch member width consistent lower outside C names raw
    lowerPaid prior minimum stable
  let θ := raw minimum
  let greatest := top branch
  let base := realized θ branch
  let release := outcomes B known gates p positive branch
  obtain ⟨ordered,paid,margin,agrees,updates⟩ :=
    exactOriginalChartPrototype B known gates p positive branch member width consistent lower outside lowerPaid
  have atLower : OriginalPrintedTerminalBitClauses.ClauseHolds f lower (lowerChart C greatest) :=
    (exactLowerRankChartRows f lower C greatest).1.mpr lowerPaid
  have atBase : OriginalPrintedTerminalBitClauses.ClauseHolds f base (lowerChart C greatest) := by
    apply (exactLowerRankChartRows f base C greatest).1.mpr
    constructor
    · intro i below
      have h : base i = lower i := agrees i below
      rw [h]
      exact lowerPaid.1 i below
    · intro i j lt below
      have eqI : base i = lower i := agrees i (lt.trans below)
      have eqJ : base j = lower j := agrees j below
      rw [eqI,eqJ]
      exact lowerPaid.2 i j lt below
  have matrixAt :
      (∃ out ∈ release, LowerMatrix f lower out) ↔ ∃ out ∈ release, LowerMatrix f base out :=
    familyTruth f lower base greatest C (candidates known gates p positive branch)
      (candidateShape known gates p positive branch) (fun i h => (agrees i h).symm)
  have charts :
      (∃ out ∈ release, GuardedAccepts f lower C greatest out) ↔
        ∃ out ∈ release, GuardedAccepts f base C greatest out := by
    constructor
    · rintro ⟨out,used,_,actual⟩
      obtain ⟨cap,present,h⟩ := matrixAt.mp ⟨out,used,actual⟩
      exact ⟨cap,present,atBase,h⟩
    · rintro ⟨out,used,_,actual⟩
      obtain ⟨cap,present,h⟩ := matrixAt.mpr ⟨out,used,actual⟩
      exact ⟨cap,present,atLower,h⟩
  have minEq : chartMinimum B θ known gates p positive branch = minimum := margin
  have stableReplay (z : Nat) (high : chartMinimum B θ known gates p positive branch ≤ z) :
      prior (replay θ known gates p branch z) ↔ prior θ := by
    have eq : replay θ known gates p branch z = raw z := updates z
    rw [minEq] at high
    rw [eq]
    exact stable z high
  have old := (exactOriginalPrintedUniformHighResidual f B selected θ known gates p plain positive paid
    branch member ordered width prior stableReplay).2
  refine (and_congr Iff.rfl charts).trans (old.trans ?_)
  constructor
  · rintro ⟨z,high,outer,source⟩
    have eq : replay θ known gates p branch z = raw z := updates z
    rw [minEq] at high
    rw [eq] at outer source
    exact ⟨z,high,outer,source⟩
  · rintro ⟨z,high,outer,source⟩
    have eq : replay θ known gates p branch z = raw z := updates z
    rw [← minEq] at high
    rw [← eq] at outer source
    exact ⟨z,high,outer,source⟩

end LogicLineages.PermittedControl.OriginalPrintedUniformLowerInput

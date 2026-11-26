module
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedReadMass
open PreparedProjection ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualCountOriginDispositions ActualZeroClassCohortTransfer ActualReadChargeIteration

def signedMass (reads : List Read) : Nat :=
  (reads.map (fun rd => rd.1.1.natAbs)).sum

/-- The normalized list contains each grouped key exactly once. Signed
cancellation may decrease, but never increase, occurrence mass. -/
def ExactNormalizedMass : Prop :=
  ∀ (f ρ : Nat → Nat) (raw xs : List Read),
    normalizeReads f ρ raw = some xs → signedMass xs ≤ signedMass raw

/-- Every original count contributes at most two reads, with the same
signed weight and, when necessary, its negation. -/
def ExactOriginMovedMass : Prop :=
  ∀ (f ρ : Nat → Nat) (anchor : Option SurvivingPrefix)
    (origins : List Origin) (ledger : List (Origin × CountDisposition)) (moved : List Read),
    DisposedOrigins f ρ anchor origins ledger moved →
    signedMass moved ≤ 2 * signedMass (origins.map Prod.fst)

def ExactZeroEdgeMass : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat) (source out : ReadState),
    ZeroEdge f B ρ r zRank source out →
    signedMass out.reads ≤ 3 * signedMass source.reads

def ExactTraceMass : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank n : Nat) (source out : ReadState),
    Trace f B ρ r zRank n source out →
    signedMass out.reads ≤ 3 ^ n * signedMass source.reads

def FullActualSignedReadMass : Prop :=
  ExactNormalizedMass ∧ ExactOriginMovedMass ∧ ExactZeroEdgeMass ∧ ExactTraceMass

end LogicLineages.PermittedControl.ActualSignedReadMass

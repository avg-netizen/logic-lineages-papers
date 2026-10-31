module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixTargets
open PredictionTapeObservation PredictionTapeRuntimeClass PredictionTapeMembershipMatrix

def ExactFiniteCertificate : Prop :=
  ∀ (code cutoff fuel : Nat), finiteCheck code cutoff fuel = true ↔
    ∀ xs : List Bool, xs.length ≤ cutoff → (boundedMove code fuel xs).isSome = true

def TotalFiniteCertificate : Prop :=
  ∀ (code : Nat), TotalBinary code → ∀ cutoff : Nat, ∃ fuel, finiteCheck code cutoff fuel = true

def EffectiveMembershipMatrix : Prop :=
  Primrec (fun z : Nat × Nat.Partrec.Code × Nat × Nat => membershipMatrix z.1 z.2.1 z.2.2.1 z.2.2.2)

def SourceMembership : Prop :=
  ∀ (code : Nat) (bound : Nat.Partrec.Code), PredictionCanonicalList.TotalNat bound →
    (RuntimeClass code (PredictionMaximum.evalValue bound) ↔
      ∃ witness : Nat, ∀ query : Nat, membershipMatrix code bound witness query = true)

end LogicLineages.ComputabilityKnowledge.PredictionTapeMembershipMatrixTargets

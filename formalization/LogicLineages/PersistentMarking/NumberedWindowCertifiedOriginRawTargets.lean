module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRawTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program evaluate)
open List.Vector
open NumberedWindowFieldAlgorithm (unpack pack)
open NumberedWindowDirectAlgorithm (Witness)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowCertifiedOriginWitnessCodecTargets (packedWitness)

def chosenAccepts (scalar : Program 1) (r : Program 3) (source cert target : Nat) : Prop :=
  evaluate (dCore scalar r permutation) (source ::ᵥ cert ::ᵥ target ::ᵥ nil) = 1

def RawSideOutcomes (scalar : Program 1) (r : Program 3)
    (rawLeft rawRight : Nat) (left right target : List Nat) : Prop :=
  (∃ (left' : List Nat) (w : Witness),
    chosenAccepts scalar r rawLeft (packedWitness w) (pack left') ∧
    target.Perm (left' ++ right)) ∨
  (∃ (right' : List Nat) (w : Witness),
    chosenAccepts scalar r rawRight (packedWitness w) (pack right') ∧
    target.Perm (left ++ right')) ∨
  (∃ (left' right' : List Nat) (wLeft wRight : Witness),
    chosenAccepts scalar r rawLeft (packedWitness wLeft) (pack left') ∧
    chosenAccepts scalar r rawRight (packedWitness wRight) (pack right') ∧
    target.Perm (left' ++ right'))

def ExactChosenNumericRawOriginCases : Prop :=
  ∀ (scalar : Program 1) (r : Program 3) (scalarTest : Nat → Bool)
      (positive : Nat → Nat → Nat → Bool),
    ScalarFit scalar scalarTest → PositiveFit r positive →
    ∀ (rawLeft rawRight rawSource rawCert rawTarget : Nat) (left right source target : List Nat),
      unpack rawLeft = some left → unpack rawRight = some right →
      unpack rawSource = some source → unpack rawTarget = some target →
      source.Perm (left ++ right) →
      chosenAccepts scalar r rawSource rawCert rawTarget →
      RawSideOutcomes scalar r rawLeft rawRight left right target

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRawTargets

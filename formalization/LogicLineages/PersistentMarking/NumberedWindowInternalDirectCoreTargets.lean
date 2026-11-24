module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt reports tripleTerm)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape rawSourceCheck observePartition)
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectInsertedScanTargets (scan)

abbrev coreTape {α : Type} (s t k r a : α) : Fin 5 → α := ![s,t,k,r,a]

def route {n : Nat} (p : Program n) (indices : Fin n → Fin 5) : Program 5 :=
  .composition p (fun i => .projection (indices i))

def boundaryAt (scalar : Program 1) : Program 5 := route (boundaryRaw scalar) ![0,1,3]
def sourceAt (count : Program 2) : Program 5 := route (rawSourceCheck (observePartition count)) ![0,2,3]
def targetAt (count : Program 2) : Program 5 := route (rawTargetCheck count) ![1,2,4]
def scanAt (positive : Program 3) : Program 5 := route (scan positive) ![4,3]

/-- Original check constituents on the common tape [source,target,kept,removed,inserted].
One and the same count observer is installed at the two ordered partitions. -/
def core (scalar : Program 1) (positive : Program 3) (count : Program 2) : Program 5 :=
  conjunction (boundaryAt scalar)
    (conjunction (sourceAt count) (conjunction (targetAt count) (scanAt positive)))

def onCert (p : Program 1) : Program 3 := .composition p ![.projection 1]
def witnessAt : Fin 5 → Program 3 :=
  ![.projection 0,.projection 2,onCert (field 0),onCert (field 1),onCert (field 2)]

/-- Actual [source, certificate, target] direct-order entry. The tag-5 guard
and all three ordered field selectors run on exactly the supplied certificate. -/
def dCore (scalar : Program 1) (positive : Program 3) (count : Program 2) : Program 3 :=
  conjunction (onCert (guardAt 5)) (.composition (core scalar positive count) witnessAt)

structure Cut (scalar : Program 1) (positive : Program 3) (count : Program 2)
    (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (s t k r a : OTerm α) : Prop where
  scalarBoundary : Nonempty (Derivation B Γ
    (programGraph (boundaryRaw scalar) (suc z) (sourceTape s t r)))
  sourceObserver : Nonempty (Derivation B Γ
    (programGraph (rawSourceCheck (observePartition count)) (suc z) (sourceTape s k r)))
  targetObserver : Nonempty (Derivation B Γ
    (programGraph (rawTargetCheck count) (suc z) (sourceTape t k a)))
  insertionScan : Nonempty (Derivation B Γ (programGraph (scan positive) (suc z) ![a,r]))

def ExactOpenCoreCut : Prop :=
  ∀ (scalar : Program 1) (positive : Program 3) (count : Program 2)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (s t k r a : OTerm α),
    Nonempty (Derivation B Γ (programGraph (core scalar positive count) (suc z) (coreTape s t k r a))) →
    Cut scalar positive count B Γ s t k r a

def ExactOpenDCore : Prop :=
  ∀ (scalar : Program 1) (positive : Program 3) (count : Program 2)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (s w t : OTerm α)
    (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (dCore scalar positive count) (suc z) (sourceTape s w t))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (k r a : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (reports 5 (w.relabel j) k r a)) →
      Nonempty (Derivation B Δ (equal (w.relabel j) (tripleTerm 5 k r a))) →
      Cut scalar positive count B Δ (s.relabel j) (t.relabel j) k r a →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreTargets

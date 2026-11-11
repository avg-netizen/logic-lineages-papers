module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransport OriginalRawVariableRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-! Exact internal arithmetic contracts for the original raw-rank Program.
All constructor metadata, cutoffs and raw inputs are unrestricted. Child ranks
are computed inside rankSum, never assumed successful. No typing, source
window, native calibration, reflection, canonicalization, I or C premise. -/

def ActualRawVariableRankVariable : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out index : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph1 variableConstructor raw index).imp
      ((graph1 variableRankRaw out raw).iff (equal out (numeral 1)))))

def ActualRawVariableRankBottom : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out tau : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph1 bottomConstructor raw tau).imp
      ((graph1 variableRankRaw out raw).iff (equal out (numeral 0)))))

def ActualRawVariableRankNil : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((programGraph nilConstructor raw Fin.elim0).imp
      ((graph1 variableRankRaw out raw).iff (equal out (numeral 0)))))

def ActualRawVariableRankLambda : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out domain child : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 lambdaConstructor raw domain child).imp
      ((graph1 variableRankRaw out raw).iff (graph1 variableRankRaw out child))))

def ActualRawVariableRankOrdinary : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out head child : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 ordinaryConstructor raw head child).imp
      ((graph1 variableRankRaw out raw).iff (graph1 variableRankRaw out child))))

def ActualRawVariableRankApplication : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out domain first second : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 applicationConstructor raw domain first second).imp
      ((graph1 variableRankRaw out raw).iff (graph2 rankSum out first second))))

def ActualRawVariableRankNumbered : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out label head tau base types extras : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((programGraph numberedConstructor raw ![label,head,tau,base,types,extras]).imp
      ((graph1 variableRankRaw out raw).iff (graph2 rankSum out base extras))))

def ActualRawVariableRankCons : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw out tau first second : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 consConstructor raw tau first second).imp
      ((graph1 variableRankRaw out raw).iff (graph2 rankSum out first second))))

/-- The public packed-rank program reads exactly the right component. -/
def ActualRawVariableRankPacked : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed out tau raw : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 InternalPairing.pairing packed tau raw).imp
      ((graph1 variableRankPackedRaw out packed).iff (graph1 variableRankRaw out raw))))

/-- Rank invariance on every arithmetic input, including malformed tags. -/
def ActualRawVariableRankShift : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw shifted rank k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 shiftRaw shifted k raw).imp
      ((graph1 variableRankRaw rank shifted).iff (graph1 variableRankRaw rank raw))))

/-- Rank invariance on every arithmetic input, including malformed tags. -/
def ActualRawVariableRankShiftPacked : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw shifted rank k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 shiftPackedRaw shifted k raw).imp
      ((graph1 variableRankPackedRaw rank shifted).iff (graph1 variableRankPackedRaw rank raw))))

/-- Erasure may merely decrement an index; strict rank decrease is not asserted. -/
def ActualRawVariableRankErase : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw erased before after d k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 eraseRaw erased d k raw ⊓
      (graph1 variableRankRaw before raw ⊓ graph1 variableRankRaw after erased)).imp
      (RankNonincrease after before)))

/-- Erasure may merely decrement an index; strict rank decrease is not asserted. -/
def ActualRawVariableRankErasePacked : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw erased before after d k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 erasePackedRaw erased d k raw ⊓
      (graph1 variableRankPackedRaw before raw ⊓ graph1 variableRankPackedRaw after erased)).imp
      (RankNonincrease after before)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTargets

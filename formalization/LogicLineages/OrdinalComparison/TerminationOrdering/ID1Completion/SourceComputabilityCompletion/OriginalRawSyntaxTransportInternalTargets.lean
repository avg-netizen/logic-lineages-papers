module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-! Every target below is an ORIGINAL object-language derivation at arbitrary
positive body, symbolic inputs and logical context. Native calibration, source
typing, C/I, successful-run, canonicality and source-window premises are absent.
The native/native-Acc proofs cannot be used as internal semantic reflection. -/

def ActualRawSyntaxInternalTotality : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (d k raw : OTerm alpha),
  Nonempty (Derivation positive Delta (existsOne
    (graph3 (fold mode) (.var (.inr 0)) (d.relabel Sum.inl) (k.relabel Sum.inl) (raw.relabel Sum.inl))))

def ActualRawSyntaxInternalFunctionality : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (out out' d k raw : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 (fold mode) out d k raw ⊓ graph3 (fold mode) out' d k raw).imp (equal out out')))

def ActualRawSyntaxInternalVariableAction : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (out d k i : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 (variableAction mode) out d k i).iff (VariableSpec mode out d k i)))

def ActualRawSyntaxInternalVariable : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k i : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph1 variableConstructor raw i).imp
      ((graph3 (fold mode) out d k raw).iff (graph3 (variableAction mode) out d k i))))

def ActualRawSyntaxInternalLambda : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k domain body bodyOut : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 lambdaConstructor raw domain body ⊓
      graph3 (fold mode) bodyOut d (OrdinaryArithmetic.succTerm k) body).imp
      ((graph3 (fold mode) out d k raw).iff
        (UnaryResult mode lambdaConstructor out domain bodyOut))))

def ActualRawSyntaxInternalApplication : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k domain fn arg fnOut argOut : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 applicationConstructor raw domain fn arg ⊓
      (graph3 (fold mode) fnOut d k fn ⊓ graph3 (fold mode) argOut d k arg)).imp
      ((graph3 (fold mode) out d k raw).iff
        (BinaryResult mode applicationConstructor out domain fnOut argOut))))

def ActualRawSyntaxInternalBottom : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k tau : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph1 bottomConstructor raw tau).imp
      ((graph3 (fold mode) out d k raw).iff (UnchangedLeafResult mode out raw))))

def ActualRawSyntaxInternalOrdinary : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k head base baseOut : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 ordinaryConstructor raw head base ⊓ graph3 (fold mode) baseOut d k base).imp
      ((graph3 (fold mode) out d k raw).iff
        (UnaryResult mode ordinaryConstructor out head baseOut))))

def ActualRawSyntaxInternalNumbered : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha))
    (raw out d k label head tau base types extras baseOut extrasOut : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((programGraph numberedConstructor raw ![label,head,tau,base,types,extras] ⊓
      (graph3 (fold mode) baseOut d k base ⊓ graph3 (fold mode) extrasOut d k extras)).imp
      ((graph3 (fold mode) out d k raw).iff
        (NumberedResult mode out label head tau baseOut types extrasOut))))

def ActualRawSyntaxInternalNil : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((programGraph nilConstructor raw Fin.elim0).imp
      ((graph3 (fold mode) out d k raw).iff (UnchangedLeafResult mode out raw))))

def ActualRawSyntaxInternalCons : Prop :=
  ∀ (positive : Positive (Fin 1)) (mode : Mode) (alpha : Type)
    (Delta : List (Formula alpha)) (raw out d k tau head tail headOut tailOut : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 consConstructor raw tau head tail ⊓
      (graph3 (fold mode) headOut d k head ⊓ graph3 (fold mode) tailOut d k tail)).imp
      ((graph3 (fold mode) out d k raw).iff
        (BinaryResult mode consConstructor out tau headOut tailOut))))

/-- Rank ignores both parameters. Shift ignores the erased-type parameter.
These graph laws connect the generic machine's lambda recursion to the public
unary rank and binary shift interfaces, without a native-calibration premise. -/
def ActualRawSyntaxInternalInterfaces : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out d k raw : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 (fold .shift) out d k raw).iff (graph2 shiftRaw out k raw))) ∧
  Nonempty (Derivation positive Delta
    ((graph3 (fold .erase) out d k raw).iff (graph3 eraseRaw out d k raw))) ∧
  Nonempty (Derivation positive Delta
    ((graph3 (fold .rank) out d k raw).iff (graph1 variableRankRaw out raw)))

/-- Packed arithmetic wrappers keep the SAME outer type on every raw input.
No Object/Gamma/canonical wrapper is asserted by this graph identity. -/
def ActualRawSyntaxInternalPacked : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed out tau raw transformed d k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 InternalPairing.pairing packed tau raw ⊓ graph2 shiftRaw transformed k raw).imp
      ((graph2 shiftPackedRaw out k packed).iff (graph2 InternalPairing.pairing out tau transformed)))) ∧
  Nonempty (Derivation positive Delta
    ((graph2 InternalPairing.pairing packed tau raw ⊓ graph3 eraseRaw transformed d k raw).imp
      ((graph3 erasePackedRaw out d k packed).iff (graph2 InternalPairing.pairing out tau transformed))))

/-- Exact domain = every arithmetic natural, justified by the frozen total raw
parser. This is cancellation BEFORE canonicalization, not source C transport. -/
def ActualRawSyntaxInternalCancellation : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw shifted erased d k : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph2 shiftRaw shifted k raw ⊓ graph3 eraseRaw erased d k shifted).imp (equal erased raw)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets

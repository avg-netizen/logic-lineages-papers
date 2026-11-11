module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open InternalPairingSumBounds (weakBound childFuelSum)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact full-output equations of the literal request and work weight ASTs.
The original arbitrary request fields and unchanged suffix are retained. -/
def ActualOriginalTypedInternalWorkFuelEquations : Prop :=
  (∀ (body : Positive (Fin 1)) (alpha : Type)
      (request mode gamma typ raw out : OTerm alpha),
    Nonempty (Derivation body []
      ((StepRequest request mode gamma typ raw).imp
        ((graph1 requestFuel out request).iff
          (equal out (OrdinaryArithmetic.succTerm raw)))))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type) (out : OTerm alpha),
    Nonempty (Derivation body []
      ((WorkFuelGraph out OrdinaryArithmetic.zeroTerm).iff
        (equal out OrdinaryArithmetic.zeroTerm)))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type)
      (workCode request mode gamma typ raw restCode tailFuel out : OTerm alpha),
    Nonempty (Derivation body []
      ((StepCons workCode request restCode ⊓
        (StepRequest request mode gamma typ raw ⊓ WorkFuelGraph tailFuel restCode)).imp
        ((WorkFuelGraph out workCode).iff
          (equal out (OrdinaryArithmetic.addTerm
            (OrdinaryArithmetic.succTerm raw) tailFuel))))))

/-- No nonempty original raw list has zero raw work weight. -/
def ActualOriginalTypedInternalWorkFuelZero : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (count workCode : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph count workCode).imp
      ((equal count OrdinaryArithmetic.zeroTerm).iff
        (equal workCode OrdinaryArithmetic.zeroTerm))))

/-- The actual raw pair chains pay precisely the child raw+1 counts.
All pair-chain variables are symbolic arithmetic terms, with no decoded
syntax, native bounds, typing evidence or successful runs as premises. -/
def ActualOriginalTypedInternalChildFuelBounds : Prop :=
  (∀ (body : Positive (Fin 1)) (alpha : Type) (raw payload domain child : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw (numeral 1) payload ⊓ StepPair payload domain child).imp
        (weakBound (OrdinaryArithmetic.succTerm child) raw)))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type)
      (raw payload children domain first second : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw (numeral 2) payload ⊓
        (StepPair payload domain children ⊓ StepPair children first second)).imp
        (weakBound (childFuelSum first second) raw)))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type) (raw payload head base : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw (numeral 4) payload ⊓ StepPair payload head base).imp
        (weakBound (OrdinaryArithmetic.succTerm base) raw)))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type)
      (raw payload a b c d label head typ base types extras : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw (numeral 5) payload ⊓
        (StepPair payload label a ⊓
          (StepPair a head b ⊓
            (StepPair b typ c ⊓
              (StepPair c base d ⊓ StepPair d types extras))))).imp
        (weakBound (childFuelSum base extras) raw)))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type)
      (raw payload children domain first second : OTerm alpha),
    Nonempty (Derivation body []
      ((StepPair raw (numeral 7) payload ⊓
        (StepPair payload domain children ⊓ StepPair children first second)).imp
        (weakBound (childFuelSum first second) raw))))

/-- All raw live nonempty states, including malformed modes, tags and failed
guards. Output work and its strictly smaller weight are CONCLUSIONS. -/
def ActualOriginalTypedInternalWorkDecrease : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (state workCode previousFuel out : OTerm alpha),
  Nonempty (Derivation body []
    ((StepLive state workCode ⊓
      ((equal workCode OrdinaryArithmetic.zeroTerm).not ⊓ WorkFuelGraph previousFuel workCode)).imp
      ((graph1 (OriginalTypedDecoder.transition H) out state).imp
        (DecreasedOrFailed out previousFuel))))

/-- Both literal terminals remain fixed through arbitrary original fuel. -/
def ActualOriginalTypedInternalTerminalFixed : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (out count terminal : OTerm alpha),
  Nonempty (Derivation body []
    ((Terminal terminal).imp
      ((graph2 (OriginalTypedDecoder.iterate H) out count terminal).iff
        (equal out terminal))))

/-- Sufficient fuel is proved internally, and the terminal endpoint and its
completed original execution are witnesses in the conclusion. -/
def ActualOriginalTypedInternalSufficientFuel : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (workCode required count : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph required workCode ⊓ weakBound required count).imp
      (TerminatedWork H count workCode)))

/-- Above the internally computed work threshold, both adding and removing
spare fuel preserve original acceptance. H is arbitrary and unchanged. -/
def ActualOriginalTypedInternalFuelSaturation : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (workCode required count : OTerm alpha),
  Nonempty (Derivation body []
    ((WorkFuelGraph required workCode ⊓ weakBound required count).imp
      ((SuccessfulWork H count workCode).iff (WorkAccepted H workCode))))

/-- Singleton weight is exactly original raw+1, and singleton acceptance
is exactly the unchanged original term/arguments checker at its own fuel. -/
def ActualOriginalTypedInternalSingletonChecker : Prop :=
  (∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (workCode request gamma typ raw : OTerm alpha),
    Nonempty (Derivation body []
      ((StepCons workCode request OrdinaryArithmetic.zeroTerm ⊓
        StepRequest request (numeral 0) gamma typ raw).imp
        ((WorkAccepted H workCode).iff
          (programGraph (OriginalTypedDecoder.termCheck H) (numeral 1) ![typ,raw,gamma]))))) ∧
  (∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
      (workCode request gamma types raw : OTerm alpha),
    Nonempty (Derivation body []
      ((StepCons workCode request OrdinaryArithmetic.zeroTerm ⊓
        StepRequest request (numeral 1) gamma types raw).imp
        ((WorkAccepted H workCode).iff
          (programGraph (OriginalTypedDecoder.argumentsCheck H) (numeral 1) ![types,raw,gamma])))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelTargets

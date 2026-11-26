module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonDepthNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateNumericProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticConcreteCheckersChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawWitnessChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonRawCodecProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowSyntax NumberedWindowRules
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowAtomicRawStepFieldProof (unpackPacked)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowArithmeticTermCode (encodeTerm decodeTerm)
open NumberedWindowArithmeticTermCodeChecks (exact_TermCodec)
open NumberedWindowArithmeticRawWitnessCode (encodeWitness decodeWitness)
open NumberedWindowArithmeticRawWitnessCodeChecks (exact_RawWitnessCodec)
open NumberedWindowArithmeticPathCheckBits (windowStepCodeBit between)
open NumberedWindowRawWitnessBits (finiteWindowWitnessBit)
open NumberedWindowRawWitnessChecks (exact_CertifiedFiniteWindowStep)
open NumberedWindowArithmeticConcreteCheckersChecks (exact_WholeTypedStep)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration packedRaw)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (typedTape)

attribute [local irreducible] NumberedWindowConcreteCheckers.step fixed

def canonicalTape (G : List Ty) (T : Ty) (q w r : Nat) : List.Vector Nat 5 :=
  typedTape (pack (G.map encodeTy)) (encodeTy T) q w r

theorem exact_OriginalPackedWindowBit (S : Spine.Signature) (K G : List Ty) (T : Ty)
    (q w r : Nat) :
    packedRaw S.entries (fixed S K) (pack (G.map encodeTy)) (encodeTy T) q w r =
      windowStepCodeBit S K G T q w r := by
  rw [packedRaw,unpackPacked]
  exact exact_WholeTypedStep S K G T q w r

/-- The compiled literal raw checker quantifies exactly the original
typed raw certificates, at the actual finite encoded lexical context. -/
theorem exact_CheckedRawWitnessExists (S : Spine.Signature) (K G : List Ty) (T : Ty)
    (p : Program 5) (fit : ActualRawCalibration S.entries (fixed S K) p) (q r : NTerm) :
    (∃ w, evaluate p (canonicalTape G T (encodeTerm q) w (encodeTerm r)) = 1) ↔
      WindowStep S K (Spine.BoundContext.«prefix» G Spine.EmptyContext) T q r := by
  have termQ := exact_TermCodec.2.1 q
  have termR := exact_TermCodec.2.1 r
  have inspect (w : Nat) :
      evaluate p (canonicalTape G T (encodeTerm q) w (encodeTerm r)) = 1 ↔
      (decodeWitness w).any (fun z => finiteWindowWitnessBit S K G T z q r) = true := by
    unfold canonicalTape typedTape
    rw [fit,exact_OriginalPackedWindowBit,windowStepCodeBit,between,termQ,termR]
    cases decodeWitness w <;> simp
  rw [← exact_CertifiedFiniteWindowStep S K G T q r]
  constructor
  · rintro ⟨w,h⟩
    have ok := (inspect w).mp h
    cases seen : decodeWitness w with
    | none => simp [seen] at ok
    | some cert => exact ⟨cert,by simpa only [seen,Option.any_some] using ok⟩
  · rintro ⟨cert,h⟩
    refine ⟨encodeWitness cert,(inspect _).mpr ?_⟩
    rw [exact_RawWitnessCodec.2.1 cert,Option.any_some]
    exact h

#print axioms exact_OriginalPackedWindowBit
#print axioms exact_CheckedRawWitnessExists
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonRawCodecProof

import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLift
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckBits
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextTargets

namespace LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowRawApplicationLift NumberedWindowRawWitnessBits
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticLeastClass (finiteC)

def ExactLiteralLift : Prop :=
  ∀ (σ τ : Ty) (U Q R : NTerm) (w : RawWitness),
    lift (encodeTy σ) (encodeTy τ) (encodeTerm U) (encodeTerm Q) (encodeWitness w) (encodeTerm R) =
      (encodeTerm (.auxApp σ τ Q U), encodeWitness (.auxFunction w), encodeTerm (.auxApp σ τ R U))

/-- The accepted step is entirely in the function slot. The argument is the
canonical raw representative of one actual fixed argument class. -/
def ExactLiftedWindowStep : Prop :=
  ∀ (S : Signature) (K Γ : List Ty) (σ τ : Ty),
    DecisionSourceUniverse.Closed K →
      ∀ (u : Class S K (finiteC Γ) σ) (argument : Nat),
        ActualCodeAt S K Γ σ argument u →
          ∀ source certificate target,
            windowStepCodeBit S K Γ (.arrow σ τ) source certificate target = true →
              let out := lift (encodeTy σ) (encodeTy τ) argument source certificate target
              windowStepCodeBit S K Γ τ out.1 out.2.1 out.2.2 = true

end LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftTargets

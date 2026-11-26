module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticHeadCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticBinderCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeTargets
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticBinderCode

def TyFuelCalibration : Prop :=
  (∀ fuel code σ, decodeTyFuel fuel code = some σ → encodeTy σ = code) ∧
  (∀ fuel σ, encodeTy σ ≤ fuel →
    decodeTyFuel fuel (encodeTy σ) = some σ)

def ExactTyCodec : Prop :=
  (∀ code σ, decodeTy code = some σ ↔ encodeTy σ = code) ∧
  (∀ σ, decodeTy (encodeTy σ) = some σ) ∧
  (∀ code, decodeTy code = none ↔ ¬ ∃ σ, encodeTy σ = code)

def ExactHeadCodec : Prop :=
  (∀ code f, decodeHead code = some f ↔ encodeHead f = code) ∧
  (∀ f, decodeHead (encodeHead f) = some f) ∧
  (∀ code, decodeHead code = none ↔ ¬ ∃ f, encodeHead f = code)

def BinderFuelCalibration : Prop :=
  (∀ fuel code Γ, decodeBindersFuel fuel code = some Γ → encodeBinders Γ = code) ∧
  (∀ fuel Γ, encodeBinders Γ ≤ fuel →
    decodeBindersFuel fuel (encodeBinders Γ) = some Γ)

def ExactBinderCodec : Prop :=
  (∀ code Γ, decodeBinders code = some Γ ↔ encodeBinders Γ = code) ∧
  (∀ Γ, decodeBinders (encodeBinders Γ) = some Γ) ∧
  (∀ code, decodeBinders code = none ↔ ¬ ∃ Γ, encodeBinders Γ = code)

/-- Numerical context input is the code of the genuine finite binder
stack, never an encoding of arbitrary lookup functions C. -/
def CodedOriginalBinderLookup : Prop := ∀ Γ i,
  codedLookup (encodeBinders Γ) i = (Spine.BoundContext.«prefix» Γ Spine.EmptyContext) i

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeTargets

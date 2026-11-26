module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathCheckBits
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPathWitnessTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckTargets
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticLeastClass
open NumberedWindowPathWitnessTargets NumberedWindowArithmeticPathCheckBits
universe u

def ExactWindowStepOnCodes : Prop :=
  ∀ S K Γ τ src dst, (∃ c, windowStepCodeBit S K Γ τ src c dst = true) ↔
    ∃ Q R, encodeTerm Q = src ∧ encodeTerm R = dst ∧ WindowStep S K (finiteC Γ) τ Q R

def ExactWindowPathOnCodes : Prop :=
  ∀ S K Γ τ src dst, (∃ c, windowPathCodeBit S K Γ τ src c dst = true) ↔
    ∃ Q R, encodeTerm Q = src ∧ encodeTerm R = dst ∧ WindowPath S K (finiteC Γ) τ Q R

def ExactClassEdgeOnCodes : Prop :=
  ∀ S K Γ τ src dst, DecisionSourceUniverse.Closed K →
    ((∃ c, classEdgeCodeBit S K Γ τ src c dst = true) ↔
      ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧ ClassEdge x y)

def ExactPositiveClassPathOnCodes : Prop :=
  ∀ S K Γ τ src dst, DecisionSourceUniverse.Closed K →
    ((∃ c, positiveClassPathCodeBit S K Γ τ src c dst = true) ↔
      ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧
        RS S K (finiteC Γ) τ x y)

def ExactPrimaryOnCodes : Prop :=
  ∀ S K Γ τ src dst, DecisionSourceUniverse.Closed K →
    (primaryCodeBit S K Γ τ src dst = true ↔
      ∃ Q R, encodeTerm Q = src ∧ encodeTerm R = dst ∧
        InWindow S K (finiteC Γ) τ Q ∧ InWindow S K (finiteC Γ) τ R ∧
        Primary S K (finiteC Γ) τ Q R)

def MissingPayload {α : Type u} (read : Nat → Option α) (src cert dst : Nat) : Prop :=
  decodeTerm src = none ∨ read cert = none ∨ decodeTerm dst = none

/-- Explicit malformed input rejection. Unadmitted least codes are
also ruled out by the exact successful class relation, independently. -/
def CodedChecksRejectMalformed : Prop :=
  (∀ S K Γ τ src cert dst, MissingPayload decodeWitness src cert dst →
    windowStepCodeBit S K Γ τ src cert dst = false) ∧
  (∀ S K Γ τ src cert dst, MissingPayload decodeRawPath src cert dst →
    windowPathCodeBit S K Γ τ src cert dst = false) ∧
  (∀ S K Γ τ src cert dst, decodeClassEdge cert = none →
    classEdgeCodeBit S K Γ τ src cert dst = false) ∧
  (∀ S K Γ τ src cert dst, decodeClassPath cert = none →
    positiveClassPathCodeBit S K Γ τ src cert dst = false) ∧
  (∀ S K Γ τ src dst, (decodeTerm src = none ∨ decodeTerm dst = none) →
    primaryCodeBit S K Γ τ src dst = false)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckTargets

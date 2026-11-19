import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCode

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckBits
open Spine NumberedWindowSyntax
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticPathCode NumberedWindowRawWitnessBits
open NumberedWindowPathWitnessBits NumberedWindowClassPathWitnessBits
open NumberedWindowTypingBits NumberedWindowPrimaryClassList
universe u

/-- Parse both original literal endpoint codes and the supplied
certificate. A malformed component rejects; no candidate is searched. -/
def between {α : Type u} (read : Nat → Option α) (test : NTerm → α → NTerm → Bool)
    (src cert dst : Nat) : Bool :=
  match decodeTerm src, read cert, decodeTerm dst with
  | some Q, some w, some R => test Q w R
  | _, _, _ => false

def windowStepCodeBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src cert dst : Nat) : Bool :=
  between decodeWitness (fun Q w R => finiteWindowWitnessBit S K Γ τ w Q R) src cert dst

def windowPathCodeBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src cert dst : Nat) : Bool :=
  between decodeRawPath (rawPathBit S K Γ τ) src cert dst

/-- The endpoints here are actual least original class codes. The
unchanged class bit independently pays successful leastCode = some. -/
def classEdgeCodeBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src cert dst : Nat) : Bool :=
  match decodeClassEdge cert with
  | some w => classEdgeBit S K Γ τ src dst w
  | none => false

def positiveClassPathCodeBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src cert dst : Nat) : Bool :=
  match decodeClassPath cert with
  | some w => positiveClassPathBit S K Γ τ src w dst
  | none => false

/-- Primary comparison starts from two actual same-context typed raw
terms, not two arbitrary quotient codes or absent decoding results. -/
def primaryCodeBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (src dst : Nat) : Bool :=
  match decodeTerm src, decodeTerm dst with
  | some Q, some R => finiteWindowBit S K Γ τ Q && finiteWindowBit S K Γ τ R &&
      primaryBit S K Γ τ Q R
  | _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckBits

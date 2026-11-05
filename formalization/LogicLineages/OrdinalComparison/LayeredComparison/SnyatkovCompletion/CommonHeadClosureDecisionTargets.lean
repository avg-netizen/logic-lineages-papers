module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionTargets
open CommonLayerSyntax CommonHeadClosureDecision

def ActualCodedClosures : Prop := ∀ (Γ : List NONote), genuineHeads Γ → ∀ (E F : Nat) (desired : Int) (b : Bool),
  (existsAnswer (headCodes Γ, E, F, desired) = some b ↔
    ((∃ ν : Nat → Nat, Int.sign ((codedValue (headCodes Γ) E ν : Int) - (codedValue (headCodes Γ) F ν : Int)) = desired) ↔ b = true)) ∧
  (forallAnswer (headCodes Γ, E, F, desired) = some b ↔
    ((∀ ν : Nat → Nat, Int.sign ((codedValue (headCodes Γ) E ν : Int) - (codedValue (headCodes Γ) F ν : Int)) = desired) ↔ b = true))

def ActualSourceClosures : Prop := ∀ (Γ : List NONote), genuineHeads Γ →
  ∀ (E F : CommonSyntax Γ.length) (desired : Int) (b : Bool),
  (existsAnswer (headCodes Γ, encodeCommon Γ.length E, encodeCommon Γ.length F, desired) = some b ↔
    ((∃ ν : Nat → Nat, Int.sign ((commonValue Γ E ν : Int) - (commonValue Γ F ν : Int)) = desired) ↔ b = true)) ∧
  (forallAnswer (headCodes Γ, encodeCommon Γ.length E, encodeCommon Γ.length F, desired) = some b ↔
    ((∀ ν : Nat → Nat, Int.sign ((commonValue Γ E ν : Int) - (commonValue Γ F ν : Int)) = desired) ↔ b = true))

def UnconditionalDecisionDomain : Prop := ∀ p : Input,
  (existsAnswer p).isSome = true ∧ (forallAnswer p).isSome = true

def ActualAllCodePrograms : Prop := Computable existsAnswer ∧ Computable forallAnswer

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionTargets

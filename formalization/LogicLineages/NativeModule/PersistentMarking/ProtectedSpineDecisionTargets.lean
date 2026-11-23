module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyTargets
public import LogicLineages.NativeModule.PersistentMarking.ConfinedPair

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineDecisionTargets
open Spine DecisionInventory DecisionRequests HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineFixedApplicationTargets
open MarkedConstructorOperator (environment leastFixedPoint)

def rootBits (S : Signature) (s t : Expr) : Bool × Bool :=
  if s.type = t.type then
    let I := inventory s t
    let E := environment s t
    let Γ := blank I.ports
    let M := leastFixedPoint S E I.sourceHeads
    let code := concreteOutput S E I.sourceHeads M Γ s.type (some s)
    let v := decode E s.type Γ code
    (v.weak Γ t,v.strict Γ t)
  else (false,false)

def supportIncluded (s t : Expr) : Bool :=
  (TypeSupport.support t).all fun τ => decide (τ ∈ TypeSupport.support s)

def confinedBits (S : Signature) (s t : Expr) : Bool × Bool :=
  let bits := rootBits S s t
  let confined := supportIncluded s t
  (bits.1 && confined,bits.2 && confined)

def Decidability : Prop := ∀ S s t σ τ,
  PaperTerm S s σ → Ordinary s → PaperTerm S t τ → Ordinary t →
  ((rootBits S s t).1 = true ↔ Weak S s t) ∧
  ((rootBits S s t).2 = true ↔ Strict S s t) ∧
  ((confinedBits S s t).1 = true ↔ ConfinedPair.Weak S s t) ∧
  ((confinedBits S s t).2 = true ↔ ConfinedPair.Strict S s t)

end LogicLineages.PersistentMarking.ProtectedSpineDecisionTargets

import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationTargets
import LogicLineages.PersistentMarking.DecisionClosureTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineAdequacyTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets
open PortNormalization
open MarkedConstructorOperator (environment leastFixedPoint)

def domain (F : Inputs S) : Environment := environment F.source F.target

def stageValue (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (q : Expr) : Value :=
  decode (domain F) q.type Γ (concreteOutput S (domain F) F.data.sourceHeads M Γ q.type (some q))

def FixedValue (S : Signature) (F : Inputs S) (Γ : Context) (q : Expr) : Value :=
  stageValue S F (leastFixedPoint S (domain F) F.data.sourceHeads) Γ q

def ExactObservation : Prop := ∀ S (F : Inputs S) Γ q t σ,
  WellFormed F.data.types F.data.ports Γ → Source F Γ q → Observed F Γ t →
  PaperTerm S q σ → PaperTerm S t σ →
  ((FixedValue S F Γ q).weak Γ t = true ↔ Weak S q t) ∧
  ((FixedValue S F Γ q).strict Γ t = true ↔ Strict S q t)

end LogicLineages.PersistentMarking.ProtectedSpineAdequacyTargets

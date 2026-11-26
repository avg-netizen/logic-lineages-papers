import LogicLineages.PersistentMarking.NumberedWindowClassPathWitnessBits

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass
open NumberedWindowPathWitnessBits NumberedWindowClassPathWitnessBits

/-- The code describes the actual quotient class if an actual admitted
representative has that successful least code. No arithmetic path/edge
checker appears in this independent endpoint relation. -/
def ActualCodeAt (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (code : Nat) (x : Class S K (finiteC Γ) τ) : Prop :=
  ∃ Q : WindowCarrier S K (finiteC Γ) τ,
    classOf Q = x ∧ leastCode S K Γ τ Q.val = some code

def ExactCertifiedFiniteRawPath : Prop :=
  ∀ S K Γ τ Q R, (∃ cert, rawPathBit S K Γ τ Q cert R = true) ↔
    WindowPath S K (finiteC Γ) τ Q R

def ExactActualClassCodeFibers : Prop :=
  ∀ S K Γ τ, DecisionSourceUniverse.Closed K →
    (∀ (x : Class S K (finiteC Γ) τ), ∃ code, ActualCodeAt S K Γ τ code x) ∧
    (∀ (x y : Class S K (finiteC Γ) τ) code,
      ActualCodeAt S K Γ τ code x → ActualCodeAt S K Γ τ code y → x = y) ∧
    (∀ (x : Class S K (finiteC Γ) τ) c d,
      ActualCodeAt S K Γ τ c x → ActualCodeAt S K Γ τ d x → c = d)

def ExactCertifiedNumericClassEdge : Prop :=
  ∀ S K Γ τ src dst, DecisionSourceUniverse.Closed K →
    ((∃ cert, classEdgeBit S K Γ τ src dst cert = true) ↔
      ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧ ClassEdge x y)

def ExactCertifiedPositiveNumericClassPath : Prop :=
  ∀ S K Γ τ src dst, DecisionSourceUniverse.Closed K →
    ((∃ cert, positiveClassPathBit S K Γ τ src cert dst = true) ↔
      ∃ x y, ActualCodeAt S K Γ τ src x ∧ ActualCodeAt S K Γ τ dst y ∧
        RS S K (finiteC Γ) τ x y)

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets

import LogicLineages.PersistentMarking.NumberedWindowOuterShape
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextTargets

namespace LogicLineages.PersistentMarking.NumberedWindowOuterShapeTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowOuterShape NumberedWindowArithmeticScalarTargets
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticAllContextTargets

def literalTag : NTerm → Nat
  | .free .. => 0
  | .bound .. => 1
  | .lam .. => 2
  | .bottom .. => 3
  | .ordinary .. => 4
  | .numbered .. => 5
  | .auxApp .. => 6

def RepresentsTag {S K C τ} (q : Class S K C τ) (tag : Nat) : Prop :=
  ∀ Q : WindowCarrier S K C τ, classOf Q = q → literalTag Q.val = tag

def ExactOuterShape : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ n tag, outerShape (fixed S K) n = some tag ↔
      ∃ (Γ : List Ty) (τ : Ty) (i : Nat) (q : Class S K (finiteC Γ) τ),
        encodeAddress ⟨Γ,τ,i⟩ = n ∧ ActualCodeAt S K Γ τ i q ∧ RepresentsTag q tag

def ExactOuterShapeReject : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ n, outerShape (fixed S K) n = none ↔ ¬ AdmittedAddress S K n

end LogicLineages.PersistentMarking.NumberedWindowOuterShapeTargets

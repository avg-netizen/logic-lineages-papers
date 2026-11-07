module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationTargets
open Source GuardCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualTypeTagPrimitive : Prop := Primrec typeTagValue

def ActualTypeTagProgram : Prop :=
  ∃ p : Program 2, ∀ v, evaluate p v = typeTagValue v

/-- All natural contexts, types and objects, with NO closure premise. -/
def ActualTypedTypeTag : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context typ object : Nat),
  JointGammaTyped.typedValue n arity (List.Vector.ofFn ![context,typ,object]) = 1 →
    typeTag context object = typ

def ActualSubtypeClosedCalibration : Prop :=
  ∀ S : List Ty, subtypeClosedTest S = true ↔ SubtypeClosed (fun tau => tau ∈ S)

def ActualValidWindowPrimitive : Prop :=
  ∀ n : Nat, Primrec (validWindowValue n)

/-- Exact acceptance and rejection, including malformed natural contexts. -/
def ActualValidWindowCalibration : Prop :=
  ∀ n context : Nat,
  (validWindow n context = 1 ↔
    ∃ ctx : OrdinaryArithmeticQuotient.Context n,
      Encodable.decode context = some ctx ∧ SubtypeClosed (fun tau => tau ∈ ctx.1.2)) ∧
  (validWindow n context = 0 ↔
    ¬ ∃ ctx : OrdinaryArithmeticQuotient.Context n,
      Encodable.decode context = some ctx ∧ SubtypeClosed (fun tau => tau ∈ ctx.1.2))

/-- Every original symbols/type/table context, with no signature or arity
assumption and no change to its existing code. -/
def ActualOriginalWindowCalibration : Prop :=
  ∀ (n : Nat) (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  validWindow n (OrdinaryArithmeticQuotient.contextCode symbols S table) = 1 ↔
    SubtypeClosed (fun tau => tau ∈ S)

def ActualValidWindowProgram : Prop :=
  ∀ n : Nat, ∃ p : Program 1, ∀ v, evaluate p v = validWindowValue n v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationTargets

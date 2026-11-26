module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorTargets
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalLambdaConstructor
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Internal arithmetic graph laws, not native-to-internal reflection. -/
def ActualOriginalLambdaConstructorFields : Prop := ConstructorFields

def ActualOriginalLambdaConstructorReconstruction : Prop := ConstructorReconstruction

/-- Separate all-input calibration of the explicit total ASTs, including
malformed packed inputs. This is not a hypothesis of either internal law. -/
def ActualOriginalLambdaConstructorRawCalibration : Prop :=
  (∀ d e b : Nat,
    evaluate constructor (List.Vector.ofFn ![d,e,b]) =
      Nat.pair (1 + Nat.pair d e)
        (Nat.pair 1 (Nat.pair d (Nat.unpair b).2))) ∧
  (∀ out : Nat,
    evaluate tag (List.Vector.ofFn ![out]) = (Nat.unpair (Nat.unpair out).2).1 ∧
    evaluate domain (List.Vector.ofFn ![out]) =
      (Nat.unpair (Nat.unpair (Nat.unpair out).2).2).1 ∧
    evaluate bodyPayload (List.Vector.ofFn ![out]) =
      (Nat.unpair (Nat.unpair (Nat.unpair out).2).2).2) ∧
  (∀ e out : Nat,
    evaluate bodyCode (List.Vector.ofFn ![e,out]) =
      Nat.pair e (Nat.unpair (Nat.unpair (Nat.unpair out).2).2).2)

/-- Exact original typed source correspondence. The body context really is
sigma::Gamma; no Encodable context extension or arithmetic membership theorem
is claimed by these numeric equations. This is only the constructor supplier
for the lambda paragraph of paper06 lem:id1, not conditional computability. -/
def ActualOriginalLambdaConstructorTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
  let b := packedNumber (⟨tau,body⟩ : NumberedRewriteReduction.Packed (Fin n) arity (sigma :: Gamma))
  let out := packedNumber (⟨.arrow sigma tau,.lam body⟩ : NumberedRewriteReduction.Packed (Fin n) arity Gamma)
  evaluate constructor (List.Vector.ofFn ![typeNumber sigma,typeNumber tau,b]) = out ∧
    evaluate tag (List.Vector.ofFn ![out]) = 1 ∧
    evaluate domain (List.Vector.ofFn ![out]) = typeNumber sigma ∧
    evaluate bodyCode (List.Vector.ofFn ![typeNumber tau,out]) = b

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorTargets

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrier
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL canonical typed carrier at fixed signature, window and Gamma.
Inputs are [value,type]. The original type decoder and canonical representative
condition are retained literally, including all rejection behavior. -/
def typedValue (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (v : List.Vector Nat 2) : Nat :=
  ((NumberedNumericDecoding.decodeType (v.get 1)).any (fun tau =>
    NumberedTypedCarrier.typedCanonicalCarrierTest n arity symbols S Gamma tau
      (v.get 0))).toNat

/-- One Program is calibrated before every natural value and type code.
This external evaluation property supplies no object-language proof rule. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (typed : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate typed v = typedValue n arity symbols S Gamma v

/-- Reuse the SAME unary source-universe leaf as the original step and
structural endpoint wrappers; it is not replaced by a packed-target test. -/
def sourceAt (validity : InternalOriginalStepGuard.Data) : Program 2 :=
  .composition validity.sourceValid (fun _ : Fin 1 => .projection 0)

/-- Literal equality of the ORIGINAL raw outer tag and supplied type code. -/
def sameOuterType : Program 2 :=
  InternalApplicationStepPeel.same (leftOf (.projection 0)) (.projection 1)

/-- Explicit exact-one conjunction, with the old canonical typed Program
retained as a leaf. This is not merely the raw carrier with a matching tag. -/
def checker (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2) : Program 2 :=
  InternalAcceptance.conjunction (sourceAt validity)
    (InternalAcceptance.conjunction sameOuterType oldTyped)

def accepted {α : Type} (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2)
    (value typ : OTerm α) : Formula α :=
  graph2 (checker validity oldTyped) InternalOriginalStepGuard.one value typ

/-- The source-universe and raw type graphs are conclusions of acceptance,
not independent semantic premises. Old canonical-typed acceptance remains. -/
def requirements {α : Type} (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2)
    (value typ : OTerm α) : Formula α :=
  graph1 validity.sourceValid InternalOriginalStepGuard.one value ⊓
    (graph1 InternalUnpair.left typ value ⊓
      graph2 oldTyped InternalOriginalStepGuard.one value typ)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrier

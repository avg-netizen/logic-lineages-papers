module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeaves
open Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ONE original context code and ONE original encoded Gamma. The ranked
signature is the only fixed family parameter; no finite window is captured. -/
def parameterCode {n : Nat} (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) : Nat :=
  Nat.pair (OrdinaryArithmeticQuotient.contextCode symbols S table) (Encodable.encode Gamma)

/-- Recover Gamma only through the ORIGINAL Object decoder on its unchanged
pair encoding. The original packed value is its second coordinate. -/
def parameterObject (value parameter : Nat) : Option ContextUniform.Object :=
  Encodable.decode (Nat.pair (Nat.unpair parameter).2 value)

/-- Preserve the ORIGINAL context decoder, including its finite-table codec.
Every malformed context or failed original Object decode returns zero. -/
def decodedValue (n : Nat)
    (f : OrdinaryArithmeticQuotient.Context n → ContextUniform.Object → Nat)
    (value parameter : Nat) : Nat :=
  match Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1,
      parameterObject value parameter with
  | some ctx, some obj => f ctx obj
  | _, _ => 0

/-- Raw presentations use only the original source-universe/packed decoders.
These are external numeric functions, never internal inference rules. -/
def sourceValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    (NumberedNumericCarrier.rawCarrierTest n arity ctx.1.1 ctx.1.2 obj.1 obj.2).toNat)
    (v.get 0) (v.get 1)

def targetValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun _ obj =>
    (NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).isSome.toNat)
    (v.get 0) (v.get 1)

/-- Target representative uses packed validity, NEVER the universe filter.
The existing raw representative is calibrated to the original least code. -/
def representativeValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
      (ContextUniformPrimary.representative arity ctx.1.1 ctx.1.2 obj.1)).getD 0)
    (v.get 0) (v.get 1)

/-- The membership input is the ORIGINAL numeric type code. Its parameter is
identical to the source/target/representative parameter. -/
def memberValue (n : Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    InternalStructuralEndpointGuard.membershipValue ctx.1.2 obj.2)
    (v.get 0) (v.get 1)

/-- All-input calibration of four binary ASTs, before selecting any windows. -/
def Calibrated (n : Nat) (arity : Fin n → Nat)
    (oldSource oldTarget oldRepresentative member : Program 2) : Prop :=
  (∀ v : List.Vector Nat 2, evaluate oldSource v = sourceValue n arity v) ∧
  (∀ v : List.Vector Nat 2, evaluate oldTarget v = targetValue n arity v) ∧
  (∀ v : List.Vector Nat 2, evaluate oldRepresentative v = representativeValue n arity v) ∧
  (∀ v : List.Vector Nat 2, evaluate member v = memberValue n v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeaves

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesTargets
open Source InternalOriginalUniformParameterLeaves
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal original codecs, with no alternative Gamma/table encoding. The
arbitrary raw parameter assertion retains the WHOLE supplied packed value. -/
def ActualOriginalUniformParameterCodec : Prop :=
  (∀ (n : Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
      (table : Fin n → Fin n → Bool) (value : Nat),
    Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
        (Nat.unpair (parameterCode symbols S Gamma table)).1 = some ((symbols,S),table) ∧
    parameterObject value (parameterCode symbols S Gamma table) = some (Gamma,value)) ∧
  (∀ value parameter : Nat, ∃ Gamma : List Ty,
    parameterObject value parameter = some (Gamma,value))

/-- ALL raw input vectors, including malformed context codes and failed
packed decodes. Equality is to wrappers around the ORIGINAL fixed-window
values, not a new successful-decode-only semantics. No hS premise is needed. -/
def ActualOriginalUniformLeafCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2),
    sourceValue n arity v = decodedValue n (fun ctx obj =>
      InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 obj.1 obj.2)
      (v.get 0) (v.get 1) ∧
    targetValue n arity v = decodedValue n (fun _ obj =>
      InternalOriginalStepGuard.targetValidityValue n arity obj.1 obj.2)
      (v.get 0) (v.get 1) ∧
    representativeValue n arity v = decodedValue n (fun ctx obj =>
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 obj.1 obj.2)
      (v.get 0) (v.get 1) ∧
    memberValue n v = decodedValue n (fun ctx obj =>
      InternalStructuralEndpointGuard.membershipValue ctx.1.2 obj.2)
      (v.get 0) (v.get 1)

/-- Genuine existence of ONE shared four-Program tuple after n/arity and
BEFORE symbols, S, Gamma and table. Every AST consumes [value,p], membership
consumes [type,p], and every exact slice includes ALL natural values. No PR,
leaf-calibration, decoding-success, subtype-closure or window premise is
supplied. This selects leaves, not a canonical fold or internal derivation. -/
def ActualOriginalUniformLeafPrograms : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ oldSource oldTarget oldRepresentative member : Program 2,
    Calibrated n arity oldSource oldTarget oldRepresentative member ∧
    ∀ (symbols : List (Fin n)) (S Gamma : List Ty)
      (table : Fin n → Fin n → Bool) (value : Nat),
      evaluate oldSource (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
        InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value ∧
      evaluate oldTarget (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
        InternalOriginalStepGuard.targetValidityValue n arity Gamma value ∧
      evaluate oldRepresentative (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
        InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value ∧
      evaluate member (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
        InternalStructuralEndpointGuard.membershipValue S value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesTargets

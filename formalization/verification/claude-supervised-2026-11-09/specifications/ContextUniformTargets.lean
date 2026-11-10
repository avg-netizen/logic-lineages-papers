module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformTargets
open Source ID1Completion.InternalCalculus ID1Completion.ContextUniform

/-- A genuinely stronger supplier than the paid fixed-Gamma program family.
No source checker, quotient equivalence, primary representative or certificate
semantics is changed; Gamma is now an encoded ordinary program input. -/
def ActualContextUniformPresentationExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ data : SourcePresentation.Data, Calibrated data n arity

/-- CURRENT WHOLE paper06 lem:id1 endpoint. One fixed-S operator and one
closed theorem cover ALL ambient contexts, including every binder extension.
The old per-Gamma targets are supporting family statements only. -/
def ActualContextUniformInternalAccessibility : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ data : SourcePresentation.Data, Calibrated data n arity ∧
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → SourceEndpoint.strictTotalPrecedence table →
  Nonempty (Derivation
    (SourcePresentation.sourceBody data (OrdinaryArithmeticQuotient.contextCode symbols S table)) []
    (SourcePresentation.allTermsFormula data (OrdinaryArithmeticQuotient.contextCode symbols S table)))

def ActualOriginalContextFibers : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context x y : Nat),
  (encodedScalar n arity context (objectCode Gamma x) ↔
    OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x) ∧
  (encodedList n arity context (objectCode Gamma x) ↔
    OrdinaryArithmeticCarrier.encodedList n arity Gamma context x) ∧
  (encodedR n arity context (objectCode Gamma x) (objectCode Gamma y) ↔
    PositiveArithmeticOperators.encodedR n arity Gamma context x y) ∧
  (encodedDirect n arity context (objectCode Gamma x) (objectCode Gamma y) ↔
    OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y)

def ActualNoCrossContextEdges : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty) (context x y : Nat),
  Gamma ≠ Delta →
  ¬ encodedR n arity context (objectCode Gamma x) (objectCode Delta y) ∧
  ¬ encodedDirect n arity context (objectCode Gamma x) (objectCode Delta y)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformTargets

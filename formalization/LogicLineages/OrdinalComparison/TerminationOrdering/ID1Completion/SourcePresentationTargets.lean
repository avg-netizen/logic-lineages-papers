module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationTargets
open Source PositiveArithmeticOperators PositiveArithmeticTransforms
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation

/-- The paid primitive-recursive suppliers assemble one actual presentation
uniformly in the encoded window. This alone is not internal derivability. -/
def ActualSourcePresentationExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ data : Data, Calibrated data n arity Gamma

/-- PENDING paper06 lem:id1, with the arithmetic presentation retained
existentially WITH its actual proof. A globally arbitrary choice of a
standard-N equivalent formula is not required to be internally adequate. -/
def ActualSourceInternalAccessibility : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ data : Data, Calibrated data n arity Gamma ∧
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → SourceEndpoint.strictTotalPrecedence table →
  Nonempty (Derivation (sourceBody data (OrdinaryArithmeticQuotient.contextCode symbols S table)) []
    (allTermsFormula data (OrdinaryArithmeticQuotient.contextCode symbols S table)))

def ActualClosedSourceOperator : Prop :=
  ∀ (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Calibrated data n arity Gamma → ∀ (context : Nat) (P : Nat → Prop) (x : Nat),
  (realize P (sourceBody data context).formula ![tagNumber false x] ↔
    OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x ∧
      ∀ y, encodedR n arity Gamma context x y → P (tagNumber false y)) ∧
  (realize P (sourceBody data context).formula ![tagNumber true x] ↔
    OrdinaryArithmeticCarrier.encodedList n arity Gamma context x ∧
      ∀ y, OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y → P (tagNumber true y))

def ActualAllTermsFormulaTruth : Prop :=
  ∀ (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Calibrated data n arity Gamma → ∀ (context : Nat) (P : Nat → Prop),
  realize P (allTermsFormula data context) Empty.elim ↔
    ∀ x, OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x → P (tagNumber false x)

/-- A soundness consumer ONLY. Its proof-tree premise is the exact missing
mathematics, and is not discharged by standard-natural semantic membership. -/
def ActualInternalSourceSoundness : Prop :=
  ∀ (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Calibrated data n arity Gamma →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  Nonempty (Derivation (sourceBody data (OrdinaryArithmeticQuotient.contextCode symbols S table)) []
    (allTermsFormula data (OrdinaryArithmeticQuotient.contextCode symbols S table))) →
  ∀ x, OrdinaryArithmeticCarrier.encodedScalar n arity Gamma
      (OrdinaryArithmeticQuotient.contextCode symbols S table) x →
    Acc (fun successor source => encodedR n arity Gamma
      (OrdinaryArithmeticQuotient.contextCode symbols S table) source successor) x

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationTargets

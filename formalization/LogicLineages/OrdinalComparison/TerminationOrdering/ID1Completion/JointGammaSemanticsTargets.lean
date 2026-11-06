module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsTargets
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open ID1Completion.InternalCalculus

/-- Exact ordinary-arithmetic compiler outputs, on every natural object code. -/
def ActualCarrierFormulaTruth : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity → ∀ (context x : Nat),
  ((SourcePresentation.checkerFormula data.scalar).Realize ![context,x] ↔
    ContextUniform.encodedScalar n arity context x) ∧
  ((SourcePresentation.checkerFormula data.multiset).Realize ![context,x] ↔
    ContextUniform.encodedList n arity context x)

/-- The original certificate graphs retain same-Gamma checks and all decoders. -/
def ActualCertificateGraphTruth : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity → ∀ (context x y : Nat),
  ((OrdinaryArithmeticQuotient.certificateGraph data.positive).Realize ![context,x,y] ↔
    ContextUniform.encodedR n arity context x y) ∧
  ((OrdinaryArithmeticQuotient.certificateGraph data.direct).Realize ![context,x,y] ↔
    ContextUniform.encodedDirect n arity context x y)

/-- One original tagged positive body ranges over all encoded ambient contexts. -/
def ActualClosedSourceOperator : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity → ∀ (context : Nat) (P : Nat → Prop) (x : Nat),
  (realize P (SourcePresentation.sourceBody data context).formula ![tagNumber false x] ↔
    ContextUniform.encodedScalar n arity context x ∧
      ∀ y, ContextUniform.encodedR n arity context x y → P (tagNumber false y)) ∧
  (realize P (SourcePresentation.sourceBody data context).formula ![tagNumber true x] ↔
    ContextUniform.encodedList n arity context x ∧
      ∀ y, ContextUniform.encodedDirect n arity context x y → P (tagNumber true y))

def ActualAllTermsFormulaTruth : Prop :=
  ∀ (data : SourcePresentation.Data) (n : Nat) (arity : Fin n → Nat),
  ContextUniform.Calibrated data n arity → ∀ (context : Nat) (P : Nat → Prop),
  realize P (SourcePresentation.allTermsFormula data context) Empty.elim ↔
    ∀ x, ContextUniform.encodedScalar n arity context x → P (tagNumber false x)

/-- Concrete Programs and their exact source-facing formula semantics, without
an added calibration assumption. This is NOT internal ID1 derivability. -/
def ActualUniformSourceFormulasExist : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : SourcePresentation.Data,
  ContextUniform.Calibrated data n arity ∧
  ∀ (context : Nat) (P : Nat → Prop),
  (∀ x,
    (realize P (SourcePresentation.sourceBody data context).formula ![tagNumber false x] ↔
      ContextUniform.encodedScalar n arity context x ∧
        ∀ y, ContextUniform.encodedR n arity context x y → P (tagNumber false y)) ∧
    (realize P (SourcePresentation.sourceBody data context).formula ![tagNumber true x] ↔
      ContextUniform.encodedList n arity context x ∧
        ∀ y, ContextUniform.encodedDirect n arity context x y → P (tagNumber true y))) ∧
  (realize P (SourcePresentation.allTermsFormula data context) Empty.elim ↔
    ∀ x, ContextUniform.encodedScalar n arity context x → P (tagNumber false x))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsTargets

module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Targets
open GorbowSyntax GorbowTheoryProof
open LogicLineages.OrdinalComparison.TerminationOrdering

/-- All free parameters, local assumptions and binders are retained. The result
is an actual ordinary Gorbow Derivation after K/S discharge, over arbitrary T. -/
def ContextTransport : Prop :=
  ∀ (T : Sentence → Prop) (alpha : Type) (Gamma : List (SourceFormula alpha))
    (phi : SourceFormula alpha) (m : Nat) (rho : alpha → Term m),
  Nonempty (ID1Completion.InternalCalculus.Derivation falseBody Gamma phi) →
  Nonempty (Derivation T
    (closeAssumptions (Gamma.map (fun a => translate a rho)) (translate phi rho)))

/-- Literal agreement with the existing ordinary-arithmetic graph translator;
this is syntax equality, with the original level-to-index binder convention. -/
def OrdinaryFormulaAgreement : Prop :=
  ∀ (alpha : Type) (phi : OrdinaryArithmetic.Formula alpha) (m : Nat) (free : alpha → Fin m),
  translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula phi)
      (fun i => Term.var (free i)) =
    GorbowOrdinaryArithmeticGraphs.translateBounded phi free Fin.elim0

/-- Empty-context arithmetical instances land in their ORIGINAL existing
Gorbow arithmetic image. This supplies no standard-model-to-proof principle. -/
def ClosedArithmeticTransport : Prop :=
  ∀ (T : Sentence → Prop) (alpha : Type) (phi : OrdinaryArithmetic.Formula alpha)
    (m : Nat) (free : alpha → Fin m),
  Nonempty (ID1Completion.InternalCalculus.Derivation falseBody []
    (PositiveArithmeticOperators.arithmeticEmbedding.onFormula phi)) →
  Nonempty (Derivation T (GorbowOrdinaryArithmeticGraphs.translateBounded phi free Fin.elim0))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Targets

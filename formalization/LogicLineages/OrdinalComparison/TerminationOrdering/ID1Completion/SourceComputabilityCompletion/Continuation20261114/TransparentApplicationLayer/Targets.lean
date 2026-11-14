module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual installed optional AST, with explicit runtime field/guard graphs.
Tags 2 and 7 are the original application and argsCons branches; answers are
literal list positions 0 and 3, not neighboring Cartesian cross answers.
This asserts neither field-supplier correctness nor global exchange closure. -/
def InternalApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha)
    (xs : Fin 19 → OTerm alpha) (tag : Nat),
  (tag = 2 ∨ tag = 7) →
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  (∀ i, Nonempty (Derivation body Delta
    (graph3 (TransparentExchangeLayer.fields U i) (xs i) node code param))) →
  Nonempty (Derivation body Delta (eqn (xs 0) (numeral tag))) →
  Nonempty (Derivation body Delta (eqn (xs 7) (numeral tag))) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  (Nonempty (Derivation body Delta
      (graph3 (TransparentExchangeLayer.optional U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn (xs 1) (xs 8) ⊓
     ((eqn (xs 6) (xs 13) ⊓ eqn h0 (numeral 1)) ⊔
      (eqn (xs 5) (xs 12) ⊓ eqn h3 (numeral 1))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentApplicationLayer.Targets

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- No spurious members in the actual flattened dependency frontier. The source
node is concluded existentially in arithmetic, not extracted as a semantic term. -/
def InternalFlattenWitness : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2)
    (frontier param out child : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) out frontier param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)) →
  Nonempty (Derivation body Delta (predecessor D frontier child param))
/-- Literal bindList successor has a genuine predecessor in the ACTUAL previous
frontier. No claimed relation to a different depth or independent child call. -/
def InternalSuccessorWitness : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (D : Program 2)
    (depth seed param frontier out child : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) frontier depth seed param)) →
  Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) out (suc depth) seed param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)) →
  Nonempty (Derivation body Delta (predecessor D frontier child param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Targets

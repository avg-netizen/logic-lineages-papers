module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Original fuel measure on every raw node and parameter. -/
def NativeRank : Prop := ∀ (v : List.Vector Nat 2), evaluate R v = (Nat.unpair (v.get 0)).2
/-- Original ordered pair-node dependency list, all raw nodes/parameters. -/
def NativeDependencies : Prop := ∀ (v : List.Vector Nat 2),
  evaluate D v = Encodable.encode (NumberedCodeEnumerationPrimrecProof.dependencies (Nat.unpair (v.get 0)))
/-- Original typed combine with its actual product/list/Option codecs and both
getD[] defaults. This does not assume two answers are present. -/
def NativeCombine : Prop := ∀ (n : Nat) (data : NumberedCodeEnumerationPrimrecSupportProof.Parameters n)
    (node : Nat × Nat) (answers : List (List (NumberedAuxiliaryCoding.Code (Fin n)))),
  evaluate (G n) (List.Vector.ofFn ![Encodable.encode node,Encodable.encode answers,Encodable.encode data]) =
    Encodable.encode (NumberedCodeEnumerationPrimrecProof.combine n data (node,answers))
/-- Every actual dependency member strictly decreases actual fuel-rank outputs.
No positive fuel, valid-node image, or known two-element list is a premise. -/
def InternalDecrease : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (node param deps child parentRank childRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 D deps node param)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)) →
  Nonempty (Derivation body Delta (graph2 R parentRank node param)) →
  Nonempty (Derivation body Delta (graph2 R childRank child param)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank))
/-- Positive branch existential is the actual new calibrated layer output, not
an external answer list. Full output graph, including impossible failure0. -/
def positiveOutput {alpha : Type} (n : Nat)
    (out ts hs ls tb vb prior opened : OTerm alpha) : Formula alpha :=
  existsOne (programGraph (OriginalEnumerationConstructorLayer.layer n) (.var (.inr 0))
    ![ts.relabel Sum.inl,hs.relabel Sum.inl,ls.relabel Sum.inl,tb.relabel Sum.inl,
      vb.relabel Sum.inl,prior.relabel Sum.inl,opened.relabel Sum.inl] ⊓
    eqn (out.relabel Sum.inl) (suc (.var (.inr 0))))
/-- Six literal source observations expose the node pair, original parameter
product, and actual lookup slots. No decoded validity or supplied layer value
is assumed, and all raw input/output terms remain arbitrary. -/
def InternalCombine : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat)
    (node answers param vb f ts hs ls tb p2 p3 prior opened out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup prior z answers)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup opened (numeral 1) answers)) →
  (Nonempty (Derivation body Delta (graph3 (G n) out node answers param)) ↔
   Nonempty (Derivation body Delta
    ((eqn f z ⊓ eqn out (numeral 1)) ⊔
      ((eqn f z).not ⊓ positiveOutput n out ts hs ls tb vb prior opened))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Targets

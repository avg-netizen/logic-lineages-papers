module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthAgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem withPairs (left right lc rc lp rp : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length lc left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length rc right)))
    (hpl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lp lc z)))
    (hpr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rp rc z))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  have he := Auxiliary.WeightedAgreementProof.agreementFold LengthWeight.weight left right lp rp ha
    (LengthWeightProof.weightedFromLength left lc lp hl hpl)
    (LengthWeightProof.weightedFromLength right rc rp hr hpr)
  have hp := headTransport InternalUnpair.left lc lp rp Fin.elim0 he (pairLeft lp lc z hpl)
  exact valueUnique InternalUnpair.left lc rc ![rp] hp (pairLeft rp rc z hpr)

def queries : Fin 2 → Program 2 :=
  ![pairOf (.projection 0) (constant 2 0),pairOf (.projection 1) (constant 2 0)]

theorem agreementLength (left right lc rc : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length lc left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length rc right))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![lc,rc] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![lc,rc] i).relabel j) = ![lc.relabel j,rc.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  have ha' := renameInto ha j Theta hj
  rw [agreementRename] at ha'
  have hl' := renameInto hl j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hl' hr'
  have hp0 := binaryRecover InternalPairing.pairing (.projection 0) (constant 2 0)
    (ys 0) (lc.relabel j) z ![lc.relabel j,rc.relabel j] (hq 0)
    (projectionValue 0 ![lc.relabel j,rc.relabel j]) (constantValue 0 ![lc.relabel j,rc.relabel j])
  have hp1 := binaryRecover InternalPairing.pairing (.projection 1) (constant 2 0)
    (ys 1) (rc.relabel j) z ![lc.relabel j,rc.relabel j] (hq 1)
    (projectionValue 1 ![lc.relabel j,rc.relabel j]) (constantValue 0 ![lc.relabel j,rc.relabel j])
  exact withPairs (left.relabel j) (right.relabel j) (lc.relabel j) (rc.relabel j)
    (ys 0) (ys 1) ha' hl' hr' hp0 hp1
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthAgreementProof

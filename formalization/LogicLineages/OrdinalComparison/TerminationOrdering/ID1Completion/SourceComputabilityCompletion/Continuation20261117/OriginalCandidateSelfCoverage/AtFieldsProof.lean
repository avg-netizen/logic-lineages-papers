module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.RequestRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceCandidatesCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.AtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem selfMember (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed parameter typ raw context gamma types out heads bounds size labels : OTerm alpha)
    (q : Request n arity H body Delta seed parameter typ raw context gamma types out)
    (hh : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed parameter)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) bounds raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing bounds size labels))) :
    Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out seed)) := by
  have hc : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed parameter)) :=
    unaryValue InternalUnpair.left (.projection 1) context parameter ![seed,parameter]
      (pairLeft parameter context gamma q.parameterPair) (projectionValue 1 ![seed,parameter])
  have hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)) :=
    unaryValue InternalUnpair.right (.projection 1) gamma parameter ![seed,parameter]
      (pairRight parameter context gamma q.parameterPair) (projectionValue 1 ![seed,parameter])
  have hr : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.seedRaw raw seed parameter)) :=
    unaryValue InternalUnpair.right (.projection 0) raw seed ![seed,parameter]
      (pairRight seed typ raw q.seedPair) (projectionValue 0 ![seed,parameter])
  have hbounds : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.bounds n) bounds seed parameter)) :=
    unaryValue (OriginalCodeBoundsRecursion.bounds n) OriginalClassCodes.seedRaw bounds raw ![seed,parameter] hb hr
  have hs : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.size n) size seed parameter)) :=
    unaryValue InternalUnpair.left (OriginalClassCodes.bounds n) size bounds ![seed,parameter]
      (pairLeft bounds size labels hp) hbounds
  have hl : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.labels n) labels seed parameter)) :=
    unaryValue InternalUnpair.right (OriginalClassCodes.bounds n) labels bounds ![seed,parameter]
      (pairRight bounds size labels hp) hbounds
  have hss : Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc size))) :=
    InternalCoprimeMultipleBoundedProof.selfLtSucc size
  have hll : Nonempty (Derivation body Delta (InternalLessThan.strictLess labels (suc labels))) :=
    InternalCoprimeMultipleBoundedProof.selfLtSucc labels
  exact OriginalSourceCandidatesCoverage.Proof.internalTermCandidates n arity H body alpha Delta
    seed parameter context gamma types heads typ raw raw seed bounds size labels size labels out
    hc hg q.typesGraph hh hs hl q.closed q.guard q.seedPair q.seedPair q.accepted q.accepted hb hp hss hll q.candidates

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.AtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.AtFieldsProof

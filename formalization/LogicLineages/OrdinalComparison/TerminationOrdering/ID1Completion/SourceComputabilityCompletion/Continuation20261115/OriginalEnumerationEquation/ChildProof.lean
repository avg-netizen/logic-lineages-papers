module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Extraction.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationCacheCoherence.SideProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.ChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open OriginalEnumerationCacheCoherence.SideProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph

theorem fromSide {child param : OTerm alpha}
    (s : Side n body Delta child param)
    (value : OTerm alpha) :
    (Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) value child param)) ↔
     Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) s.table child))) :=
  OriginalEnumerationEquation.Extraction.Proof.alignedExtraction n
    body alpha Delta child param s.index s.seed s.seedRank s.depth s.frontier s.table value
    s.rankGraph s.bounded s.subtraction s.front s.member s.tableGraph

theorem atPrevious {node param : OTerm alpha}
    (s : Side n body Delta node param)
    (pred old next deps child value : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (eqn s.index (suc pred))))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph
      OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D
      (OriginalEnumerationRecursionInterface.G n)) old s.index s.seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList
      OriginalEnumerationRecursionInterface.D) next (suc s.depth) s.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    (Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) value child param)) ↔
     Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc value) old child))) := by
  let cs := previousSide s pred old next child hi ho hf (childMember s deps child next hd hm hf)
  exact fromSide cs value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.ChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.ChildProof

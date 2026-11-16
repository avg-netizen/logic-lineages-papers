module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRankSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn add)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem edgeDescent (node child param parentRank childRank : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (ExchangeFrontierWitness.dependencyEdge dependency)
      (numeral 1) node child param)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank node param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) := by
  apply programCases dependency (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hd
  rw [strictRename]
  simp only [consTermRename,emptyRename] at hd
  have hej := renameInto he j Theta hj
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hej
  have hpj := renameInto hp j Theta hj
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hpj hcj
  let xs : Fin 3 → OTerm beta := Fin.cons (node.relabel j) (Fin.cons (child.relabel j) (Fin.cons (param.relabel j) Fin.elim0))
  have harg := binaryValue dependency (.projection 0) (.projection 2)
    deps (node.relabel j) (param.relabel j) xs hd (projectionValue 0 xs) (projectionValue 2 xs)
  have hm := binaryRecover contains (.composition dependency ![.projection 0,.projection 2])
    (.projection 1) (numeral 1) deps (child.relabel j) xs hej harg (projectionValue 1 xs)
  exact RankDescentProof.descent (node.relabel j) (param.relabel j) deps (child.relabel j)
    (parentRank.relabel j) (childRank.relabel j) hpj hd hm hcj

theorem zeroAt (seed param frontier child seedRank childRank listCode : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier z seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hr : Nonempty (Derivation body Delta (graph2 rank childRank child param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode seed z))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (add z childRank) seedRank)) := by
  have hz := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero dependency seed param listCode hc
  have he := valueUnique (ExchangeFrontier.bindList dependency) frontier listCode ![z,seed,param] hf hz
  have hl := headTransport contains (numeral 1) frontier listCode (Fin.cons child Fin.elim0) he hm
  have hcs := PrimaryCarrierBound.RunProof.singletonMember listCode seed child hc hl
  have hrt := headTransport rank childRank child seed (Fin.cons param Fin.elim0) hcs hr
  obtain ⟨heq⟩ := valueUnique rank childRank seedRank ![seed,param] hrt hs
  exact ⟨InternalQuotientComparisonProof.orRight (trans (InternalAdditionLawsProof.leftZero childRank) heq)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRankSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRankSupportProof

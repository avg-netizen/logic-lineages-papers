module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalAdditionLawsProof (leftZero)
open Continuation20261114
open InductionDefinitions InductionSyntaxProof BindingProof
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)


theorem edgeDescent (n : Nat) (node child param parentRank childRank : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (ExchangeFrontierWitness.dependencyEdge (OriginalDecodedDependencies.dependencies n))
      (numeral 1) node child param)))
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) parentRank node param)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) := by
  apply programCases (OriginalDecodedDependencies.dependencies n) (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hd
  rw [strictRename]
  simp only [consTermRename,emptyRename] at hd
  have hej := InternalGraphCompositionFunctionalityProof.renameInto he j Theta hj
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hej
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  let xs : Fin 3 → OTerm beta := Fin.cons (node.relabel j) (Fin.cons (child.relabel j) (Fin.cons (param.relabel j) Fin.elim0))
  have harg := binaryValue (OriginalDecodedDependencies.dependencies n) (.projection 0) (.projection 2)
    deps (node.relabel j) (param.relabel j) xs hd (projectionValue 0 xs) (projectionValue 2 xs)
  have hm := binaryRecover contains (.composition (OriginalDecodedDependencies.dependencies n) ![.projection 0,.projection 2])
    (.projection 1) (numeral 1) deps (child.relabel j) xs hej harg (projectionValue 1 xs)
  exact OriginalDecodedRank.Proof.rankDecrease n body beta Theta (node.relabel j) (param.relabel j) deps
    (child.relabel j) (parentRank.relabel j) (childRank.relabel j) hd hm hrj hcj

theorem zeroAt (n : Nat) (seed param frontier child seedRank childRank listCode : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier z seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hn : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) childRank child param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode seed z))) :
    Nonempty (Derivation body Delta (result z seedRank childRank)) := by
  have hz := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero (OriginalDecodedDependencies.dependencies n) seed param listCode hc
  have he := valueUnique (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier listCode ![z,seed,param] hf hz
  have hl := headTransport contains (numeral 1) frontier listCode (Fin.cons child Fin.elim0) he hm
  have hcs := PrimaryCarrierBound.RunProof.singletonMember listCode seed child hc hl
  have hnr := headTransport (OriginalDecodedRank.rank n) childRank child seed (Fin.cons param Fin.elim0) hcs hn
  obtain ⟨hrr⟩ := valueUnique (OriginalDecodedRank.rank n) childRank seedRank (Fin.cons seed (Fin.cons param Fin.elim0)) hnr hr
  exact ⟨InternalQuotientComparisonProof.orRight (trans (leftZero childRank) hrr)⟩

theorem zeroCore (n : Nat) (seed param frontier child seedRank childRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier z seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hn : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) childRank child param))) :
    Nonempty (Derivation body Delta (result z seedRank childRank)) := by
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta listCode hj hc
  simp only [resultRename,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hc
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hnj := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  exact zeroAt n (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j)
    (seedRank.relabel j) (childRank.relabel j) listCode hrj hfj hmj hnj hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.SupportProof

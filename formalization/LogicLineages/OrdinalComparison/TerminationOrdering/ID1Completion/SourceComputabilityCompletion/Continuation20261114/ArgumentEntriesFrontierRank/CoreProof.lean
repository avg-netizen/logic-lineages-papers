module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.CoreProof
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
open InductionDefinitions InductionSyntaxProof BindingProof
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)

theorem edgeDescent (node child param : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (ExchangeFrontierWitness.dependencyEdge ArgumentEntriesFrontier.dependency)
      (numeral 1) node child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child node)) := by
  apply programCases ArgumentEntriesFrontier.dependency (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hd
  rw [strictRename]
  simp only [consTermRename,emptyRename] at hd
  have hej := renameInto he j Theta hj
  simp only [graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hej
  let xs : Fin 3 → OTerm beta := Fin.cons (node.relabel j) (Fin.cons (child.relabel j) (Fin.cons (param.relabel j) Fin.elim0))
  have harg := binaryValue ArgumentEntriesFrontier.dependency (.projection 0) (.projection 2)
    deps (node.relabel j) (param.relabel j) xs hd (projectionValue 0 xs) (projectionValue 2 xs)
  have hm := binaryRecover contains (.composition ArgumentEntriesFrontier.dependency ![.projection 0,.projection 2])
    (.projection 1) (numeral 1) deps (child.relabel j) xs hej harg (projectionValue 1 xs)
  exact ArgumentEntriesDependencyDescent.Proof.dependencyDescent body beta Theta
    (node.relabel j) (param.relabel j) deps (child.relabel j) hd hm

theorem zeroAt (seed param frontier child listCode : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier z seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode seed z))) :
    Nonempty (Derivation body Delta (result z seed child)) := by
  have hz := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero ArgumentEntriesFrontier.dependency seed param listCode hc
  have he := valueUnique (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier listCode ![z,seed,param] hf hz
  have hl := headTransport contains (numeral 1) frontier listCode (Fin.cons child Fin.elim0) he hm
  obtain ⟨hcs⟩ := PrimaryCarrierBound.RunProof.singletonMember listCode seed child hc hl
  exact ⟨InternalQuotientComparisonProof.orRight (trans (leftZero child) hcs)⟩

theorem zeroCore (seed param frontier child : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier z seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child))) :
    Nonempty (Derivation body Delta (result z seed child)) := by
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta listCode hj hc
  simp only [resultRename,zRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hc
  have hfj := renameInto hf j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph3Rename,zRelabel] at hfj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact zeroAt (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) listCode hfj hmj hc

theorem successorAt (depth seed param frontier child previous : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) previous depth seed param))) :
    Nonempty (Derivation body Delta (result (suc depth) seed child)) := by
  have hw := ExchangeFrontierWitness.Proof.successorWitness body alpha Delta ArgumentEntriesFrontier.dependency
    depth seed param previous frontier child hp hf hm
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness (ExchangeFrontierWitness.dependencyEdge ArgumentEntriesFrontier.dependency)
    previous child param _ hw
  intro beta j Theta node hj hmem hedge
  simp only [resultRename,sucRelabel]
  have hij := renameInto hi j Theta hj
  rw [atCountRename] at hij
  have hpj := renameInto hp j Theta hj
  rw [graph3Rename] at hpj
  have hb := rowApply (depth.relabel j) (seed.relabel j) (param.relabel j) (previous.relabel j) node hij hpj hmem
  exact PrimaryFiniteDescent.ArithmeticProof.budgetStep (depth.relabel j) node (child.relabel j) (seed.relabel j)
    (edgeDescent node (child.relabel j) (param.relabel j) hedge) hb

theorem successorCore (depth seed param frontier child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (AtCount depth)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc depth) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child))) :
    Nonempty (Derivation body Delta (result (suc depth) seed child)) := by
  apply programCases (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency)
    (Fin.cons depth (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta previous hj hp
  simp only [resultRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hij := renameInto hi j Theta hj
  rw [atCountRename] at hij
  have hfj := renameInto hf j Theta hj
  simp only [graph3Rename,sucRelabel] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact successorAt (depth.relabel j) (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) previous hij hfj hmj hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.CoreProof

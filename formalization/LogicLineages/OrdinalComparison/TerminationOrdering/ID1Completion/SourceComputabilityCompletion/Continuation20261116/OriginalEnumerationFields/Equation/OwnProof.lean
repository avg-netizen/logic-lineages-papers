module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.CoverageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.OwnProof
open Continuation20261115.OriginalDecodedExchangeEquation
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open Continuation20261114
open OriginalEnumerationFields.CacheCoherence.SideProof
open AgreementDefinitions AgreementSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat)
attribute [local irreducible] programGraph

theorem atWitnesses (node param rank old deps final nodes next : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps node param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) final (suc rank) node param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes node z)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) next (suc z) node param)))
    : Nonempty (Derivation body Delta (lookupAgreement (OriginalEnumerationFields.extract n) deps param old)) := by
  let root : Side n body Delta node param := {
    index := rank, seed := node, seedRank := rank, depth := z, frontier := nodes, table := final,
    rankGraph := hr,
    bounded := PrimaryUncoveredCount.OrderProof.reflexive rank,
    subtraction := InternalEqualityTestSubtractionProof.subtractSelf rank,
    front := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero _ node param nodes hc,
    member := containsHit nodes node z node hc (by simpa only [equalEqn] using (Nonempty.intro (refl node) : Nonempty (Derivation body Delta (eqn node node)))),
    tableGraph := ht }
  apply zeroSuccessorCases Delta rank _
  · exact CoverageProof.zero n node param rank old deps (withHyp hr (eqn rank z))
      (withHyp hd (eqn rank z)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro beta j Theta pred hj hp
    rw [agreementRename]
    let rn := root.rename j Theta hj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    rw [graph2Rename] at hdj
    have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
    simp only [graph3Rename,sucRelabel,zRelabel] at hfj
    exact CoverageProof.positive n rn pred (old.relabel j) (next.relabel j) (deps.relabel j) hp hoj (by simpa only [rn, Side.rename, root, zRelabel] using hfj) hdj

theorem atNodes (node param rank old deps final nodes : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps node param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) final (suc rank) node param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes node z)))
    : Nonempty (Derivation body Delta (lookupAgreement (OriginalEnumerationFields.extract n) deps param old)) := by
  apply programCases (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) (Fin.cons (suc z) (Fin.cons node (Fin.cons param Fin.elim0))) _
  intro beta j Theta next hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [agreementRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hcj
  exact atWitnesses n (node.relabel j) (param.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) (final.relabel j) (nodes.relabel j) next hrj hoj hdj htj hcj hx

theorem atFinal (node param rank old deps final : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps node param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) final (suc rank) node param)))
    : Nonempty (Derivation body Delta (lookupAgreement (OriginalEnumerationFields.extract n) deps param old)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons node (Fin.cons z Fin.elim0)) _
  intro beta j Theta nodes hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [agreementRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  exact atNodes n (node.relabel j) (param.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) (final.relabel j) nodes hrj hoj hdj htj hx

theorem agreement (node param rank old deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps node param)))
    : Nonempty (Derivation body Delta (lookupAgreement (OriginalEnumerationFields.extract n) deps param old)) := by
  apply programCases (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) (Fin.cons (suc rank) (Fin.cons node (Fin.cons param Fin.elim0))) _
  intro beta j Theta final hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [agreementRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdj
  exact atFinal n (node.relabel j) (param.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) final hrj hoj hdj hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.OwnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.OwnProof

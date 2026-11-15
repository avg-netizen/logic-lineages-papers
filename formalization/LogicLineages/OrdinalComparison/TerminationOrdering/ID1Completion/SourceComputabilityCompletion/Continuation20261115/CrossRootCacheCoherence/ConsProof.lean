module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SideProof PresenceProof InputProof
theorem atLists {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 old1 old2 next1 next2 rest deps : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    (ho2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 c.s2.index c.s2.seed param)))
    (hn1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next1 (suc c.s1.depth) c.s1.seed param)))
    (hn2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next2 (suc c.s2.depth) c.s2.seed param)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest c.tail z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps c.head rest)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  have hdeps := SupportProof.dependencyAtLists raw c.tau c.head c.tail param rest deps c.constructor hr hd
  exact ConsFrameProof.close {
    s1 := c.s1, s2 := c.s2, tau := c.tau, head := c.head, tail := c.tail,
    pred1 := pred1, pred2 := pred2, old1 := old1, old2 := old2, next1 := next1, next2 := next2,
    deps := deps, found := c.found, constructor := c.constructor, index1 := hi1, index2 := hi2,
    oldGraph1 := ho1, oldGraph2 := ho2, nextGraph1 := hn1, nextGraph2 := hn2,
    dependency := andLeft hdeps, headMember := andLeft (andRight hdeps), tailMember := andRight (andRight hdeps),
    below := c.below, lookup := c.lookup }

theorem atDepsInput {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 old1 old2 next1 next2 rest : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    (ho2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 c.s2.index c.s2.seed param)))
    (hn1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next1 (suc c.s1.depth) c.s1.seed param)))
    (hn2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next2 (suc c.s2.depth) c.s2.seed param)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest c.tail z)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode (Fin.cons c.head (Fin.cons rest Fin.elim0)) _
  intro beta j Theta deps hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi2j
  have ho1j := InternalGraphCompositionFunctionalityProof.renameInto ho1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho1j
  have ho2j := InternalGraphCompositionFunctionalityProof.renameInto ho2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho2j
  have hn1j := InternalGraphCompositionFunctionalityProof.renameInto hn1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hn1j
  have hn2j := InternalGraphCompositionFunctionalityProof.renameInto hn2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hn2j
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hrj
  exact atLists (c.rename j Theta hj) (pred1.relabel j) (pred2.relabel j) (old1.relabel j) (old2.relabel j) (next1.relabel j) (next2.relabel j) (rest.relabel j) deps hi1j hi2j ho1j ho2j hn1j hn2j hrj hx

theorem atRestInput {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 old1 old2 next1 next2 : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    (ho2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 c.s2.index c.s2.seed param)))
    (hn1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next1 (suc c.s1.depth) c.s1.seed param)))
    (hn2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next2 (suc c.s2.depth) c.s2.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply InternalAcceptanceSupportProof.programCases InternalListCodec.consCode (Fin.cons c.tail (Fin.cons z Fin.elim0)) _
  intro beta j Theta rest hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi2j
  have ho1j := InternalGraphCompositionFunctionalityProof.renameInto ho1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho1j
  have ho2j := InternalGraphCompositionFunctionalityProof.renameInto ho2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho2j
  have hn1j := InternalGraphCompositionFunctionalityProof.renameInto hn1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hn1j
  have hn2j := InternalGraphCompositionFunctionalityProof.renameInto hn2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hn2j
  exact atDepsInput (c.rename j Theta hj) (pred1.relabel j) (pred2.relabel j) (old1.relabel j) (old2.relabel j) (next1.relabel j) (next2.relabel j) rest hi1j hi2j ho1j ho2j hn1j hn2j hx

theorem atNext2Input {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 old1 old2 next1 : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    (ho2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 c.s2.index c.s2.seed param)))
    (hn1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next1 (suc c.s1.depth) c.s1.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply InternalAcceptanceSupportProof.programCases (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) (Fin.cons (suc c.s2.depth) (Fin.cons c.s2.seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta next2 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi2j
  have ho1j := InternalGraphCompositionFunctionalityProof.renameInto ho1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho1j
  have ho2j := InternalGraphCompositionFunctionalityProof.renameInto ho2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho2j
  have hn1j := InternalGraphCompositionFunctionalityProof.renameInto hn1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hn1j
  exact atRestInput (c.rename j Theta hj) (pred1.relabel j) (pred2.relabel j) (old1.relabel j) (old2.relabel j) (next1.relabel j) next2 hi1j hi2j ho1j ho2j hn1j hx

theorem atNext1Input {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 old1 old2 : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    (ho2 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old2 c.s2.index c.s2.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply InternalAcceptanceSupportProof.programCases (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) (Fin.cons (suc c.s1.depth) (Fin.cons c.s1.seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta next1 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi2j
  have ho1j := InternalGraphCompositionFunctionalityProof.renameInto ho1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho1j
  have ho2j := InternalGraphCompositionFunctionalityProof.renameInto ho2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho2j
  exact atNext2Input (c.rename j Theta hj) (pred1.relabel j) (pred2.relabel j) (old1.relabel j) (old2.relabel j) next1 hi1j hi2j ho1j ho2j hx

theorem atOld2Input {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 old1 : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    (ho1 : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old1 c.s1.index c.s1.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply InternalAcceptanceSupportProof.programCases ArgumentEntriesRecursor.graph (Fin.cons c.s2.index (Fin.cons c.s2.seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta old2 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi2j
  have ho1j := InternalGraphCompositionFunctionalityProof.renameInto ho1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at ho1j
  exact atNext1Input (c.rename j Theta hj) (pred1.relabel j) (pred2.relabel j) (old1.relabel j) old2 hi1j hi2j ho1j hx

theorem atOld1Input {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 pred2 : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn c.s2.index (suc pred2))))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply InternalAcceptanceSupportProof.programCases ArgumentEntriesRecursor.graph (Fin.cons c.s1.index (Fin.cons c.s1.seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta old1 hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hi2j
  exact atOld2Input (c.rename j Theta hj) (pred1.relabel j) (pred2.relabel j) old1 hi1j hi2j hx

theorem atFirstIndex {raw param : OTerm alpha} (c : ConsInput body Delta raw param) (pred1 : OTerm alpha)
    (hi1 : Nonempty (Derivation body Delta (eqn c.s1.index (suc pred1)))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply zeroSuccessorCases Delta c.s2.index _
  · obtain ⟨hn⟩ := index2Nonzero c
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta pred2 hj hi2
    rw [graph2Rename]
    have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
    simp only [eqnRelabel,sucRelabel] at hi1j
    exact atOld1Input (c.rename j Theta hj) (pred1.relabel j) pred2 hi1j hi2

theorem close {raw param : OTerm alpha} (c : ConsInput body Delta raw param) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup c.found c.s2.table raw)) := by
  apply zeroSuccessorCases Delta c.s1.index _
  · obtain ⟨hn⟩ := index1Nonzero c
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta pred1 hj hi1
    rw [graph2Rename]
    exact atFirstIndex (c.rename j Theta hj) pred1 hi1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsProof

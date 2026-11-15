module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.ValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atWitnesses (raw tau head tail param tailValue value pred final old nodes rest deps next headValue answers : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head rest)))
    (hnext : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next (suc z) raw param)))
    (hheadValue : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract headValue head param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  have hm := containsHit nodes raw z raw hnodes
    (by simpa only [InternalControlGraphSupportProof.equalEqn] using (Nonempty.intro (refl raw) : Nonempty (Derivation body Delta (eqn raw raw))))
  let root : CrossRootCacheCoherence.SideProof.Side body Delta raw param := {
    index := raw, seed := raw, depth := z, frontier := nodes, table := final,
    bounded := PrimaryUncoveredCount.OrderProof.reflexive raw,
    subtraction := InternalEqualityTestSubtractionProof.subtractSelf raw,
    front := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero _ raw param nodes hnodes,
    member := hm, tableGraph := hfinal }
  have hd := CrossRootCacheCoherence.SupportProof.dependencyAtLists raw tau head tail param rest deps hc hrest hdeps
  let sh := CrossRootCacheCoherence.SideProof.previousSide root pred old next head hp hold hnext
    (CrossRootCacheCoherence.SideProof.childMember root deps head next (andLeft hd) (andLeft (andRight hd)) hnext)
  let st := CrossRootCacheCoherence.SideProof.previousSide root pred old next tail hp hold hnext
    (CrossRootCacheCoherence.SideProof.childMember root deps tail next (andLeft hd) (andRight (andRight hd)) hnext)
  have hh : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)) := by
    simpa only [sh,CrossRootCacheCoherence.SideProof.previousSide] using
      (SupportProof.fromSide head param headValue sh hheadValue)
  have ht' : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old tail)) := by
    simpa only [st,CrossRootCacheCoherence.SideProof.previousSide] using
      (SupportProof.fromSide tail param tailValue st ht)
  have ha := (ArgumentEntriesOrderedAnswers.Proof.consAnswers body alpha Delta raw tau head tail param deps old headValue tailValue answers
    hc (andLeft hd) hh ht' hanswers).2
  have hg := ArgumentEntriesTailCoherence.SupportProof.layerAtTail raw answers param tailValue value ha hv
  exact ArgumentEntriesConsTable.FinalProof.finalAnswers body alpha Delta ArgumentEntriesRecursor.rank
    ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer raw param raw old deps answers value
    (projectionValue 0 ![raw,param]) hold (andLeft hd) hanswers hg

theorem at7 (raw tau head tail param tailValue value pred final old nodes rest deps next headValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head rest)))
    (hnext : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next (suc z) raw param)))
    (hheadValue : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract headValue head param)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old (Fin.elim0))) _
  intro beta j Theta answers hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnodesj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hrestj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hdepsj
  have hnextj := renameInto hnext j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnextj
  have hheadValuej := renameInto hheadValue j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hheadValuej
  exact atWitnesses (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) (old.relabel j) (nodes.relabel j) (rest.relabel j) (deps.relabel j) (next.relabel j) (headValue.relabel j) answers hcj htj hvj hpj hfinalj holdj hnodesj hrestj hdepsj hnextj hheadValuej hx

theorem at6 (raw tau head tail param tailValue value pred final old nodes rest deps next : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head rest)))
    (hnext : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) next (suc z) raw param)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons head (Fin.cons param (Fin.elim0))) _
  intro beta j Theta headValue hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnodesj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hrestj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hdepsj
  have hnextj := renameInto hnext j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnextj
  exact at7 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) (old.relabel j) (nodes.relabel j) (rest.relabel j) (deps.relabel j) (next.relabel j) headValue hcj htj hvj hpj hfinalj holdj hnodesj hrestj hdepsj hnextj hx

theorem at5 (raw tau head tail param tailValue value pred final old nodes rest deps : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head rest)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) (Fin.cons (suc z) (Fin.cons raw (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta next hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnodesj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hrestj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hdepsj
  exact at6 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) (old.relabel j) (nodes.relabel j) (rest.relabel j) (deps.relabel j) next hcj htj hvj hpj hfinalj holdj hnodesj hrestj hdepsj hx

theorem at4 (raw tau head tail param tailValue value pred final old nodes rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons rest (Fin.elim0))) _
  intro beta j Theta deps hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnodesj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hrestj
  exact at5 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) (old.relabel j) (nodes.relabel j) (rest.relabel j) deps hcj htj hvj hpj hfinalj holdj hnodesj hrestj hx

theorem at3 (raw tau head tail param tailValue value pred final old nodes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons tail (Fin.cons z (Fin.elim0))) _
  intro beta j Theta rest hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hnodesj
  exact at4 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) (old.relabel j) (nodes.relabel j) rest hcj htj hvj hpj hfinalj holdj hnodesj hx

theorem at2 (raw tau head tail param tailValue value pred final old : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons raw (Fin.cons z (Fin.elim0))) _
  intro beta j Theta nodes hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at holdj
  exact at3 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) (old.relabel j) nodes hcj htj hvj hpj hfinalj holdj hx

theorem at1 (raw tau head tail param tailValue value pred final : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    (hfinal : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph final (suc raw) raw param)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons raw (Fin.cons raw (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta old hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  have hfinalj := renameInto hfinal j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hfinalj
  exact at2 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) (final.relabel j) old hcj htj hvj hpj hfinalj hx

theorem at0 (raw tau head tail param tailValue value pred : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue)))
    (hp : Nonempty (Derivation body Delta (eqn raw (suc pred))))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons (suc raw) (Fin.cons raw (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta final hj hx
  rw [graph2Rename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hcj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at htj
  have hvj := renameInto hv j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hvj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,eqnRelabel] at hpj
  exact at1 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (tailValue.relabel j) (value.relabel j) (pred.relabel j) final hcj htj hvj hpj hx

theorem consValue (raw tau head tail param tailValue value : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step value raw tailValue))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw param)) := by
  apply zeroSuccessorCases Delta raw _
  · obtain ⟨hn⟩ := SupportProof.rawNonzero raw tau head tail hc
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta pred hj hp
    rw [graph2Rename]
    have hcj := renameInto hc j Theta hj
    rw [graph3Rename] at hcj
    have htj := renameInto ht j Theta hj
    rw [graph2Rename] at htj
    have hvj := renameInto hv j Theta hj
    rw [graph2Rename] at hvj
    exact at0 (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
      (tailValue.relabel j) (value.relabel j) pred hcj htj hvj hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.ValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneConsExtraction.ValueProof

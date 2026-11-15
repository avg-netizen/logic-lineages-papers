module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.ConsFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InputProof
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
open SideProof PresenceProof

structure Input (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (raw param : OTerm alpha) where
  s1 s2 : Side body Delta raw param
  found : OTerm alpha
  below : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw raw))
  lookup : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw))

def Input.rename {raw param : OTerm alpha} (c : Input body Delta raw param)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) : Input body Theta (raw.relabel j) (param.relabel j) where
  s1 := c.s1.rename j Theta hj
  s2 := c.s2.rename j Theta hj
  found := c.found.relabel j
  below := by
    have h := renameInto c.below j Theta hj
    simpa only [InductionSyntaxProof.belowRawRename] using h
  lookup := by
    have h := renameInto c.lookup j Theta hj
    simpa only [graph2Rename] using h

structure ConsInput (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha)) (raw param : OTerm alpha)
    extends Input body Delta raw param where
  tau head tail : OTerm alpha
  constructor : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail))

def ConsInput.rename {raw param : OTerm alpha} (c : ConsInput body Delta raw param)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) : ConsInput body Theta (raw.relabel j) (param.relabel j) where
  toInput := c.toInput.rename j Theta hj
  tau := c.tau.relabel j
  head := c.head.relabel j
  tail := c.tail.relabel j
  constructor := by
    have h := renameInto c.constructor j Theta hj
    simpa only [graph3Rename] using h

theorem index1Nonzero {raw param : OTerm alpha} (c : ConsInput body Delta raw param) :
    Nonempty (Derivation body Delta (eqn c.s1.index z).not) :=
  SupportProof.indexNonzero raw c.tail c.s1.index (SupportProof.consTailStrict raw c.tau c.head c.tail c.constructor)
    (FrontierCapacity.Proof.capacity body alpha Delta c.s1.index c.s1.seed param c.s1.depth c.s1.frontier raw
      c.s1.bounded c.s1.subtraction c.s1.front c.s1.member)

theorem index2Nonzero {raw param : OTerm alpha} (c : ConsInput body Delta raw param) :
    Nonempty (Derivation body Delta (eqn c.s2.index z).not) :=
  SupportProof.indexNonzero raw c.tail c.s2.index (SupportProof.consTailStrict raw c.tau c.head c.tail c.constructor)
    (FrontierCapacity.Proof.capacity body alpha Delta c.s2.index c.s2.seed param c.s2.depth c.s2.frontier raw
      c.s2.bounded c.s2.subtraction c.s2.front c.s2.member)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.InputProof

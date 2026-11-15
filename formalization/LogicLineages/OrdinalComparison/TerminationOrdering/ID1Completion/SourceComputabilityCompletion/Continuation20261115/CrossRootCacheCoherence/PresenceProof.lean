module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SideProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.PresenceProof
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
open SideProof

theorem presentCases {raw param : OTerm alpha} (s : Side body Delta raw param) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (value : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ExchangeMapGraph.lookup (suc value) (s.table.relabel j) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalAcceptanceSupportProof.programCases ExchangeMapGraph.lookup (Fin.cons s.table (Fin.cons raw Fin.elim0)) _
  intro beta j Theta found hj hf
  simp only [consTermRename,emptyRename] at hf
  have sn := s.rename j Theta hj
  have hn := lookupNonzero sn found hf
  apply zeroSuccessorCases Theta found _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro gamma k Xi value hk he
    have hfr := InternalGraphCompositionFunctionalityProof.renameInto hf k Xi hk
    rw [graph2Rename] at hfr
    have hp := outputTransport ExchangeMapGraph.lookup (found.relabel k) (suc value)
      (Fin.cons ((s.table.relabel j).relabel k) (Fin.cons ((raw.relabel j).relabel k) Fin.elim0)) he hfr
    have hm : ∀ q ∈ Delta, q.relabel (k ∘ j) ∈ Xi := by
      intro q hq
      have h := hk (q.relabel j) (hj q hq)
      simpa only [formulaRelabelComposition] using h
    have hresult := step gamma (k ∘ j) Xi value hm (by simpa only [Term.relabel_relabel] using hp)
    simpa only [formulaRelabelComposition] using hresult

theorem packFields {raw param : OTerm alpha} (s1 s2 : Side body Delta raw param) (found : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw))) :
    Nonempty (Derivation body Delta (InductionDefinitions.fields raw param s1.index s1.seed s1.depth s1.frontier s1.table
      s2.index s2.seed s2.depth s2.frontier s2.table found)) :=
  andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (s1.bounded) s1.subtraction) s1.front) s1.member) s1.tableGraph) s2.bounded) s2.subtraction) s2.front) s2.member) s2.tableGraph) hl

theorem smallerApply {raw child param : OTerm alpha} (s1 s2 : Side body Delta child param) (found : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw raw)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table child))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table child)) :=
  BindingProof.belowRawApply raw child param s1.index s1.seed s1.depth s1.frontier s1.table
    s2.index s2.seed s2.depth s2.frontier s2.table found hi hs (packFields s1 s2 found hl)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.PresenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.PresenceProof

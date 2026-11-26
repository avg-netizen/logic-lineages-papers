module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.SideProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.ZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat} {arity : Fin n → Nat} {V : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3}
attribute [local irreducible] programGraph
theorem noMemberAt {raw param : OTerm alpha}
    (rank deps child childRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) childRank child param)))
    (hi : Nonempty (Derivation body Delta (eqn rank z))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hcap := PrimaryUncoveredCount.OrderProof.reflexive (body := body) (Delta := Delta) rank
  have hlt := OriginalDecodedRank.Proof.rankDecrease n body alpha Delta raw param deps child rank childRank hd hm hr hc
  obtain ⟨hn⟩ := CrossRootCacheCoherence.SupportProof.indexNonzero rank childRank rank hlt hcap
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination hn hi⟩

theorem noMember {raw param : OTerm alpha}
    (rank deps child : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hi : Nonempty (Derivation body Delta (eqn rank z))) :
    Nonempty (Derivation body Delta ⊥) := by
  apply programCases (OriginalDecodedRank.rank n) (Fin.cons child (Fin.cons param Fin.elim0)) _
  intro beta j Theta childRank hj hc
  simp only [consTermRename,emptyRename] at hc
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  simp only [eqnRelabel,zRelabel] at hij
  exact noMemberAt (rank.relabel j) (deps.relabel j) (child.relabel j) childRank hrj hdj hmj hc hij

theorem dependencyZero {raw param : OTerm alpha}
    (rank deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps raw param)))
    (hi : Nonempty (Derivation body Delta (eqn rank z))) :
    Nonempty (Derivation body Delta (eqn deps z)) := by
  apply OriginalContextInsertionLengthProof.listCases deps _
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro beta j Theta head tail hj hc
    rw [eqnRelabel,zRelabel]
      have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    rw [graph2Rename] at hrj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    rw [graph2Rename] at hdj
    have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
    simp only [eqnRelabel,zRelabel] at hij
    obtain ⟨bad⟩ := noMember (rank.relabel j) (deps.relabel j) head hrj hdj
      (OriginalMapGraphTransport.RestrictionProof.headMember (deps.relabel j) head tail hc) hij
    exact ⟨Derivation.explosion bad⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.ZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.ZeroProof

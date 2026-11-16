module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.SideProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.RankProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.RestrictionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.ZeroProof
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
open Continuation20261114 SideProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph
theorem noMemberAt {raw param : OTerm alpha} (s : Side n body Delta raw param)
    (rank deps child childRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank childRank child param)))
    (hi : Nonempty (Derivation body Delta (eqn s.index z))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hcap := SideProof.capacity s rank hr
  have hlt := RankProof.rankDecrease body alpha Delta raw param deps child rank childRank hd hm hr hc
  obtain ⟨hn⟩ := CrossRootCacheCoherence.SupportProof.indexNonzero rank childRank s.index hlt hcap
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination hn hi⟩

theorem noMember {raw param : OTerm alpha} (s : Side n body Delta raw param)
    (rank deps child : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hi : Nonempty (Derivation body Delta (eqn s.index z))) :
    Nonempty (Derivation body Delta ⊥) := by
  apply programCases OriginalEnumerationDepth.rank (Fin.cons child (Fin.cons param Fin.elim0)) _
  intro beta j Theta childRank hj hc
  simp only [consTermRename,emptyRename] at hc
  let sn := s.rename j Theta hj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
  simp only [eqnRelabel,zRelabel] at hij
  exact noMemberAt sn (rank.relabel j) (deps.relabel j) (child.relabel j) childRank hrj hdj hmj hc hij

theorem dependencyZero {raw param : OTerm alpha} (s : Side n body Delta raw param)
    (rank deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps raw param)))
    (hi : Nonempty (Derivation body Delta (eqn s.index z))) :
    Nonempty (Derivation body Delta (eqn deps z)) := by
  apply OriginalContextInsertionLengthProof.listCases deps _
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro beta j Theta head tail hj hc
    rw [eqnRelabel,zRelabel]
    let sn := s.rename j Theta hj
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    rw [graph2Rename] at hrj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    rw [graph2Rename] at hdj
    have hij := InternalGraphCompositionFunctionalityProof.renameInto hi j Theta hj
    simp only [eqnRelabel,zRelabel] at hij
    obtain ⟨bad⟩ := noMember sn (rank.relabel j) (deps.relabel j) head hrj hdj
      (OriginalMapGraphTransport.RestrictionProof.headMember (deps.relabel j) head tail hc) hij
    exact ⟨Derivation.explosion bad⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.ZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CacheCoherence.ZeroProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.OrderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalAdditionLawsProof InternalSourceInversionSupportProof
open InternalOriginalOrderProof InternalOriginalOrderSyntaxProof
open InternalEqualityTestSubtractionSupportProof InternalEqualityTestSubtractionProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem complementAt (index seed depth gap : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn (add index gap) seed)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed))) :
    Nonempty (Derivation body Delta (eqn (add index depth) seed)) := by
  have hg := subTransport gap index (add index gap) index seed ⟨refl index⟩ he (diagonal index gap)
  obtain ⟨hv⟩ := valueUnique InternalEqualityTest.subtract depth gap
    (Fin.cons index (Fin.cons seed Fin.elim0)) hd hg
  obtain ⟨he⟩ := he
  exact ⟨trans (congAddLeft index hv) he⟩

theorem complementStrict (index seed depth : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (ltF index seed)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed))) :
    Nonempty (Derivation body Delta (eqn (add index depth) seed)) := by
  apply orderCases Delta index seed _ hb
  intro beta j Theta gap hj he
  simp only [eqnRelabel,addRelabel]
  have hdj := renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  exact complementAt (index.relabel j) (seed.relabel j) (depth.relabel j) (suc gap) he hdj

theorem complement : Targets.InternalComplement := by
  intro body alpha Delta index seed depth hb hd
  obtain ⟨hb⟩ := hb
  have hl : Nonempty (Derivation body (ltF index seed :: Delta) (eqn (add index depth) seed)) :=
    complementStrict index seed depth ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hd _)
  have he : Nonempty (Derivation body (eqn index seed :: Delta) (eqn (add index depth) seed)) := by
    have hz : Nonempty (Derivation body (eqn index seed :: Delta) (eqn (add index z) seed)) :=
      ⟨trans (addZero index) (Derivation.hypothesis List.mem_cons_self)⟩
    exact complementAt index seed depth z hz (withHyp hd _)
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hb
    (Derivation.implicationIntroduction (Classical.choice hl))
    (Derivation.implicationIntroduction (Classical.choice he))⟩

theorem predecessorAlignment : Targets.InternalPredecessorAlignment := by
  intro body alpha Delta index seed depth hb hd
  obtain ⟨he⟩ := complement body alpha Delta (suc index) seed depth hb hd
  have hs : Nonempty (Derivation body Delta (eqn (add index (suc depth)) seed)) :=
    ⟨trans (addSucc index depth) (trans (symm (leftSuccessor index depth)) he)⟩
  exact subTransport (suc depth) index (add index (suc depth)) index seed
    ⟨refl index⟩ hs (diagonal index (suc depth))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.Proof

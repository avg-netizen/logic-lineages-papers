module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.SubtractionAlignment.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.BoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.OrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalAdditionLawsProof InternalAdditionCancellationProof
open InternalSourceInversionSupportProof InternalOriginalOrderProof InternalOriginalOrderSyntaxProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem strictCancel (a x y : InternalGraphComposition.OTerm alpha)
    (h : Nonempty (Derivation body Delta (ltF (add a x) (add a y)))) :
    Nonempty (Derivation body Delta (ltF x y)) := by
  apply orderCases Delta (add a x) (add a y) _ h
  intro beta j Theta gap hj he
  simp only [orderRename]
  simp only [addRelabel] at he
  obtain ⟨he⟩ := he
  have hc := trans (symm (associativity (a.relabel j) (x.relabel j) (suc gap))) he
  have hg := Derivation.implicationElimination (leftCancellation (add (x.relabel j) (suc gap)) (y.relabel j) (a.relabel j)) hc
  apply actualOriginalOrderIntroduction body beta Theta (x.relabel j) (y.relabel j) gap
  rw [onEquality]
  exact ⟨hg⟩

theorem boundedCancel (a x y : InternalGraphComposition.OTerm alpha)
    (h : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (add a x) (add a y)))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded x y)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := strictCancel (body := body) (Delta := ltF (add a x) (add a y) :: Delta) a x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he : Derivation body (eqn (add a x) (add a y) :: Delta) (eqn x y) :=
    Derivation.implicationElimination (leftCancellation x y a) (Derivation.hypothesis List.mem_cons_self)
  exact ⟨InternalBetaTotalityProof.disjunctionElimination h
    (Derivation.implicationIntroduction (orLeft hl))
    (Derivation.implicationIntroduction (orRight he))⟩

theorem capacity : Targets.InternalCapacity := by
  intro body alpha Delta index seed param depth frontier node hb hs hf hn
  obtain ⟨hc⟩ := SubtractionAlignment.Proof.complement body alpha Delta index seed depth hb hs
  have hr := ArgumentEntriesFrontierRank.BoundProof.rankBound body alpha Delta depth seed param frontier node hf hn
  have he : Nonempty (Derivation body Delta (eqn seed (add depth index))) :=
    ⟨trans (symm hc) (commutativity index depth)⟩
  have ht := PrimaryUncoveredCount.OrderProof.transport (add depth node) seed (add depth node) (add depth index)
    ⟨refl _⟩ he hr
  exact boundedCancel depth node index ht

theorem alignedPreviousCoverage : Targets.InternalAlignedPreviousCoverage := by
  intro body alpha Delta index seed param depth frontier previous node deps child found hb hs hf hp hn hd hc hl
  have ha := SubtractionAlignment.Proof.predecessorAlignment body alpha Delta index seed depth hb hs
  exact ArgumentEntriesPreviousCoverage.Proof.previousCoverage body alpha Delta index seed param depth frontier previous node deps child found
    ha hf hp hn hd hc hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.Proof

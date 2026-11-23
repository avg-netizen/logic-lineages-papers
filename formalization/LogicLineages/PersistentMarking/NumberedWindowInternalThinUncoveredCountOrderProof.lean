module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperators (Positive)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculus (Derivation Formula)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalScratchInclusionThinProof (included includedRename includedSubst)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalAdditionLawsProof InternalUnpairArithmeticProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
private theorem orRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

@[simp] theorem boundedRename {alpha beta : Type} (a b : OTerm alpha) (j : alpha → beta) :
    (bounded a b).relabel j = bounded (a.relabel j) (b.relabel j) := by
  unfold bounded
  rw [orRename (ltF a b) (eqn a b) j, orderRename, eqnRelabel]

theorem reflexive (a : OTerm alpha) : Nonempty (Derivation body Delta (bounded a a)) :=
  ⟨orRight (InternalTagArithmeticSupportProof.refl a)⟩

theorem transport (a b x y : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (eqn a x)))
    (hb : Nonempty (Derivation body Delta (eqn b y)))
    (h : Nonempty (Derivation body Delta (bounded a b))) :
    Nonempty (Derivation body Delta (bounded x y)) := by
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  obtain ⟨h⟩ := h
  have hl : Derivation body (ltF a b :: Delta) (bounded x y) :=
    orLeft (orderRight x (addHyp hb _) (orderLeft b (addHyp ha _) (Derivation.hypothesis List.mem_cons_self)))
  have he : Derivation body (eqn a b :: Delta) (bounded x y) :=
    orRight (InternalTagArithmeticSupportProof.trans (InternalTagArithmeticSupportProof.symm (addHyp ha _))
      (InternalTagArithmeticSupportProof.trans (Derivation.hypothesis List.mem_cons_self) (addHyp hb _)))
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction he)⟩

theorem strictSucc (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (ltF a b))) :
    Nonempty (Derivation body Delta (ltF (suc a) (suc b))) := by
  obtain ⟨h⟩ := addStrictLeft (suc z) a b h
  have ea : Derivation body Delta (eqn (add (suc z) a) (suc a)) :=
    InternalTagArithmeticSupportProof.trans (leftSuccessor z a) (congSuc (leftZero a))
  have eb : Derivation body Delta (eqn (add (suc z) b) (suc b)) :=
    InternalTagArithmeticSupportProof.trans (leftSuccessor z b) (congSuc (leftZero b))
  exact ⟨orderRight (suc a) eb (orderLeft (add (suc z) b) ea h)⟩

theorem successor (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (bounded a b))) :
    Nonempty (Derivation body Delta (bounded (suc a) (suc b))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := strictSucc (body := body) (Delta := ltF a b :: Delta) a b
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction (orLeft hl))
    (Derivation.implicationIntroduction (orRight (congSuc (Derivation.hypothesis List.mem_cons_self))))⟩

theorem strictNext (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (bounded a b))) :
    Nonempty (Derivation body Delta (ltF a (suc b))) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := rightSuccessor (body := body) (Gamma := ltF a b :: Delta) a b
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := InternalCoprimeMultipleBoundedProof.selfLtSucc (body := body) (Gamma := eqn a b :: Delta) b
  have he := orderLeft (suc b) (InternalTagArithmeticSupportProof.symm (Derivation.hypothesis (body := body)
    (Gamma := eqn a b :: Delta) List.mem_cons_self)) hn
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction he)⟩

theorem rightSuccessorBound (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (bounded a b))) :
    Nonempty (Derivation body Delta (bounded a (suc b))) := by
  obtain ⟨h⟩ := strictNext a b h
  exact ⟨orLeft h⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof

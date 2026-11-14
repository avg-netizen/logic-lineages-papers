module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.OrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalAdditionLawsProof InternalUnpairArithmeticProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
@[simp] theorem boundedRename {alpha beta : Type} (a b : OTerm alpha) (j : alpha → beta) :
    (bounded a b).relabel j = bounded (a.relabel j) (b.relabel j) := by
  simp only [bounded,PrimaryExpansionSoundness.AppendSyntaxProof.orRename,orderRename,eqnRelabel]

theorem reflexive (a : OTerm alpha) : Nonempty (Derivation body Delta (bounded a a)) :=
  ⟨orRight (refl a)⟩

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
    orRight (trans (symm (addHyp ha _)) (trans (Derivation.hypothesis List.mem_cons_self) (addHyp hb _)))
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction he)⟩

theorem strictSucc (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (ltF a b))) :
    Nonempty (Derivation body Delta (ltF (suc a) (suc b))) := by
  obtain ⟨h⟩ := addStrictLeft (suc z) a b h
  have ea : Derivation body Delta (eqn (add (suc z) a) (suc a)) :=
    trans (leftSuccessor z a) (congSuc (leftZero a))
  have eb : Derivation body Delta (eqn (add (suc z) b) (suc b)) :=
    trans (leftSuccessor z b) (congSuc (leftZero b))
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
  have he := orderLeft (suc b) (symm (Derivation.hypothesis (body := body)
    (Gamma := eqn a b :: Delta) List.mem_cons_self)) hn
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction hl) (Derivation.implicationIntroduction he)⟩

theorem rightSuccessorBound (a b : OTerm alpha)
    (h : Nonempty (Derivation body Delta (bounded a b))) :
    Nonempty (Derivation body Delta (bounded a (suc b))) := by
  obtain ⟨h⟩ := strictNext a b h
  exact ⟨orLeft h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.OrderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.OrderProof

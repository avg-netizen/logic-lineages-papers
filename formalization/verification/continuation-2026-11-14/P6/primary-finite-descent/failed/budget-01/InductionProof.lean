module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InductionDefinitions.Induction InductionSyntaxProof InductionStepProof InductionCoreProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rowZero (E : Program 3) :
    Nonempty (Derivation body Delta (AtCount E z)) := by
  apply introduction body alpha 7 Delta
  let pool : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let initial : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let next : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let initialRemaining : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let remaining : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := fields E z pool initial parameter out next initialRemaining remaining
  have h : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨hz⟩ := zeroCore E pool initial parameter out next initialRemaining remaining
    ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight h))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))⟩
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction hz)

theorem rowSuccessor (E : Program 3) (elapsed : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E elapsed))) :
    Nonempty (Derivation body Delta (AtCount E (suc elapsed))) := by
  apply introduction body alpha 7 Delta
  let pool : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
  let initial : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
  let next : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
  let initialRemaining : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
  let remaining : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
  let A := fields E (suc (elapsed.relabel Sum.inl)) pool initial parameter out next initialRemaining remaining
  have h : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  have hr := renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 7)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at hr
  obtain ⟨hs⟩ := successorCore E (elapsed.relabel Sum.inl) pool initial parameter out next initialRemaining remaining
    (withHyp hr A) ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight h))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight h))⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction hs)

theorem allCounts (E : Program 3) (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount E count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount E k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (rowZero (body := body) (Delta := Delta) E)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := rowSuccessor (body := body) (Delta := theta :: Delta.map weaken) E k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

theorem iterationBudget : Targets.IterationBudget := by
  intro E body alpha Delta elapsed pool initial parameter out next initialRemaining remaining hi he hinit hrem
  exact rowApply E elapsed pool initial parameter out next initialRemaining remaining
    (allCounts E elapsed) hi he hinit hrem

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionProof

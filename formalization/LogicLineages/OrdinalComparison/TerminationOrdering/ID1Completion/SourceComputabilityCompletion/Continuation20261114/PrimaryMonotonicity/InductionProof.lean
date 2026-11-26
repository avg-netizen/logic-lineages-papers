module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InductionDefinitions InductionSyntaxProof InductionCoreProof
open InternalTagArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rowZero (E : Program 3) : Nonempty (Derivation body Delta (AtCount E z)) := by
  apply introduction body alpha 6 Delta
  let pool : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 0)
  let left : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 1)
  let right : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 3)
  let leftOut : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 4)
  let rightOut : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields E z pool left right parameter leftOut rightOut
  have h : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨hz⟩ := zeroCore E pool left right parameter leftOut rightOut
    ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction hz)

theorem rowSuccessor (E : Program 3) (count : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count))) :
    Nonempty (Derivation body Delta (AtCount E (suc count))) := by
  apply introduction body alpha 6 Delta
  let pool : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 0)
  let left : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 1)
  let right : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 3)
  let leftOut : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 4)
  let rightOut : OrdinaryArithmetic.Term (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := fields E (suc (count.relabel Sum.inl)) pool left right parameter leftOut rightOut
  have h : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  have hr := renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 6)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at hr
  obtain ⟨hs⟩ := successorCore E (count.relabel Sum.inl) pool left right parameter leftOut rightOut
    (withHyp hr A) ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction hs)

theorem allCounts (E : Program 3) (count : OrdinaryArithmetic.Term alpha) :
    Nonempty (Derivation body Delta (AtCount E count)) := by
  let k : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
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

theorem iterationMonotonicity : Targets.IterationMonotonicity := by
  intro E body alpha Delta count pool left right parameter leftOut rightOut hi hl hr
  exact rowApply E count pool left right parameter leftOut rightOut (allCounts E count) hi hl hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionProof

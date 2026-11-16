module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BoundProof
open Continuation20261114
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalAdditionLawsProof (leftZero)
open InductionDefinitions InductionSyntaxProof BindingProof
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)

open CoreProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (bindEmbedding varBind nextTerm nextEmbedding)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem rowZero : Nonempty (Derivation body Delta (AtCount z)) := by
  apply introduction body alpha 6 Delta
  let seed : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let frontier : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let child : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let seedRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let childRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := InductionDefinitions.fields (z) seed param frontier child seedRank childRank
  have hA : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := andLeft (andLeft (andLeft hA))
  have hm := andRight (andLeft (andLeft hA))
  have hs := andRight (andLeft hA)
  have hc := andRight hA
  obtain ⟨h⟩ := zeroCore seed param frontier child seedRank childRank hf hm hs hc
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem rowSuccessor (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount count))) :
    Nonempty (Derivation body Delta (AtCount (suc count))) := by
  apply introduction body alpha 6 Delta
  let seed : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
  let frontier : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
  let child : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
  let seedRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
  let childRank : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
  let A := InductionDefinitions.fields (suc (count.relabel Sum.inl)) seed param frontier child seedRank childRank
  have hr := renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 6)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at hr
  have hA : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := andLeft (andLeft (andLeft hA))
  have hm := andRight (andLeft (andLeft hA))
  have hs := andRight (andLeft hA)
  have hc := andRight hA
  obtain ⟨h⟩ := successorCore (count.relabel Sum.inl) seed param frontier child seedRank childRank (withHyp hr A) hf hm hs hc
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem allCounts (count : OTerm alpha) :
    Nonempty (Derivation body Delta (AtCount count)) := by
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := AtCount k
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using
      (rowZero (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := rowSuccessor (body := body) (Delta := theta :: Delta.map weaken) k
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,k,successorInstance,nextEmbedding,atCountSubst,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,k,instantiate,bindEmbedding,atCountSubst,varBind] using Nonempty.intro h

theorem rankBound (depth seed param frontier child seedRank childRank : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hs : Nonempty (Derivation body Delta (graph2 rank seedRank seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 rank childRank child param))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (OrdinaryArithmetic.addTerm depth childRank) seedRank)) :=
  rowApply depth seed param frontier child seedRank childRank (allCounts depth) hf hm hs hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.FrontierRank.BoundProof

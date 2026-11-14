module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.RecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open Induction InductionSyntaxProof PrimaryIteration.RecursionProof
open InternalBetaTotalityProof InternalQuotientComparisonProof
open PrimaryIteration (iterate)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rowApply (E : Program 3) (count pool reached parameter out needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtCount E count)))
    (hi : Nonempty (Derivation body Delta (graph4 (iterate E) out count pool reached parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result reached pool needle)) := by
  obtain ⟨h⟩ := elimination body alpha 5 Delta (matrix E count)
    (fun i => emb (![pool,reached,parameter,out,needle] i)) h
  rw [InductionSyntaxProof.matrixWitness] at h
  obtain ⟨hf⟩ := andIntro hi hm
  exact ⟨Derivation.implicationElimination h hf⟩

theorem zeroCore (E : Program 3) (pool reached parameter out needle : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 (iterate E) out z pool reached parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result reached pool needle)) := by
  obtain ⟨he⟩ := valueUnique (iterate E) out reached ![z,pool,reached,parameter]
    hi (zeroValue E pool reached parameter)
  obtain ⟨hm'⟩ := headTransport contains (suc z) out reached (Fin.cons needle Fin.elim0) ⟨he⟩ hm
  exact ⟨orLeft hm'⟩

theorem successorCore (E : Program 3) (count pool reached parameter out needle : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count)))
    (hi : Nonempty (Derivation body Delta (graph4 (iterate E) out (suc count) pool reached parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result reached pool needle)) := by
  apply programCases (iterate E) (Fin.cons count (Fin.cons pool (Fin.cons reached (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta previous hj hr
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hr
  have hrow' := renameInto hrow j Theta hj
  rw [atCountRename] at hrow'
  have hi' := renameInto hi j Theta hj
  simp only [graph4Rename,sucRelabel] at hi'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hm'
  have he := successorRecover E (count.relabel j) previous (out.relabel j)
    (pool.relabel j) (reached.relabel j) (parameter.relabel j) hr hi'
  obtain ⟨hd⟩ := PrimaryExpansionSoundness.Proof.expansionSoundness E (pool.relabel j) previous
    (parameter.relabel j) (out.relabel j) (needle.relabel j) he hm'
  let A := graph2 contains (suc z) previous (needle.relabel j)
  let B := graph2 contains (suc z) (pool.relabel j) (needle.relabel j) ⊓
    PrimaryExpansionSoundness.sourceWitness E previous (needle.relabel j) (parameter.relabel j)
  obtain ⟨hp⟩ := rowApply E (count.relabel j) (pool.relabel j) (reached.relabel j)
    (parameter.relabel j) previous (needle.relabel j) (withHyp hrow' A) (withHyp hr A)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Derivation body (B :: Theta) B := Derivation.hypothesis List.mem_cons_self
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hp)
    (Derivation.implicationIntroduction (orRight (Derivation.conjunctionLeft hb)))⟩

theorem rowZero (E : Program 3) : Nonempty (Derivation body Delta (AtCount E z)) := by
  apply introduction body alpha 5 Delta
  let pool : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let reached : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let needle : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields E z pool reached parameter out needle
  obtain ⟨h⟩ := zeroCore (body := body)
    (Delta := A :: Delta.map (fun p => p.relabel Sum.inl)) E pool reached parameter out needle
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [matrix,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem rowSuccessor (E : Program 3) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E count))) :
    Nonempty (Derivation body Delta (AtCount E (suc count))) := by
  apply introduction body alpha 5 Delta
  let pool : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let reached : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let needle : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields E (suc (count.relabel Sum.inl)) pool reached parameter out needle
  have hr := renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 5)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [atCountRename] at hr
  obtain ⟨h⟩ := successorCore E (count.relabel Sum.inl) pool reached parameter out needle
    (withHyp hr A) ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [matrix,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

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

theorem iterationCarrier : Targets.IterationCarrier := by
  intro E body alpha Delta count pool reached parameter out needle hi hm
  exact rowApply E count pool reached parameter out needle (allCounts E count) hi hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.InductionProof

module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOriginProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn eqnRelabel eqnSubst z zRelabel zSubst sucRelabel sucSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename consTermRename)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalCoverAscendingRangeOriginDataProof (nilHit)
open NumberedWindowInternalCoverCartesianFoldOriginTargets (blockHit)
open NumberedWindowInternalCoverCartesianFoldOriginChecks (exact_OpenCartesianFoldOrigin)
open NumberedWindowInternalCoverCartesianFoldOriginWitnessProof (blockMemberOfHit)
open NumberedWindowInternalCoverNamedLeafOriginBindingProof (cartesianCases)
open NumberedWindowInternalCoverTypeLeavesTargets
open NumberedWindowInternalCoverTypeLeavesOpenDataProof

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}

private theorem numeralSubst (n : Nat) (ts : α → OTerm β) :
    (numeral n : OTerm α).subst ts = numeral n := by
  induction n with
  | zero => exact zSubst ts
  | succ n ih => simpa only [numeral,sucSubst] using congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

private theorem rawConsSubst (a b : OTerm α) (ts : α → OTerm β) :
    (rawCons a b).subst ts = rawCons (a.subst ts) (b.subst ts) := by
  unfold rawCons pairTerm
  simp only [sucSubst,addSubst,mulSubst]

private theorem rowSubst (K key ty : OTerm α) (ts : α → OTerm β) :
    (typeLeafOriginRow K key ty).subst (fun x => emb (ts x)) =
      typeLeafOriginRow (K.subst ts) (key.subst ts) (ty.subst ts) := by
  simp only [typeLeafOriginRow,conjunctionSubst,memberSubst,eqnSubst,typeLeafTerm,
    rawConsSubst,zSubst,numeralSubst]

private theorem rowRename (K key ty : OTerm α) (j : α → β) :
    (typeLeafOriginRow K key ty).relabel j =
      typeLeafOriginRow (K.relabel j) (key.relabel j) (ty.relabel j) := by
  simp only [typeLeafOriginRow,conjunctionRename,graphRename,eqnRelabel,termRename]

private theorem originRename (K key : OTerm α) (j : α → β) :
    (typeLeafOrigin K key).relabel j = typeLeafOrigin (K.relabel j) (key.relabel j) := by
  change (existsOne (typeLeafOriginBinder K key)).relabel j =
    existsOne (typeLeafOriginBinder (K.relabel j) (key.relabel j))
  rw [existsRename]
  apply congrArg existsOne
  unfold typeLeafOriginBinder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

private theorem introduce (K key ty : OTerm α)
    (typed : Derivation body Γ (memberGraph K ty))
    (same : Derivation body Γ (eqn (typeLeafTerm ty) key)) :
    Nonempty (Derivation body Γ (typeLeafOrigin K key)) := by
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := typeLeafOriginBinder K key) (emb ty)
  simp only [instantiate,bindEmbedding,typeLeafOriginBinder,rowSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction typed same

private theorem singletonKey (one ty key : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph one (typeLeafTerm ty) z)))
    (hit : Nonempty (Derivation body Γ (memberGraph one key))) :
    Nonempty (Derivation body Γ (eqn (typeLeafTerm ty) key)) := by
  let n := typeLeafTerm ty
  obtain ⟨split⟩ := consInversion one n z key cell hit
  let H := (missGraph n key).not
  let T := memberGraph z key
  obtain ⟨same⟩ := nonzeroEquality (body := body) (Γ := H :: Γ) n key
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨bottom⟩ := nilHit (body := body) (Γ := T :: Γ) key
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction same)
    (Derivation.implicationIntroduction (Derivation.explosion bottom))⟩

private theorem atType (K key ty : OTerm α)
    (ht : Nonempty (Derivation body Γ (memberGraph K ty)))
    (hit : Nonempty (Derivation body Γ (blockHit (k := 0) typeLeafSingleton ty key Fin.elim0))) :
    Nonempty (Derivation body Γ (typeLeafOrigin K key)) := by
  apply programCases typeLeafSingleton (unaryTape ty) _
  intro β j Δ one keep actual
  rw [originRename]
  rw [oneTapeRename] at actual
  have ht' := renameInto ht j Δ keep
  rw [graphRename] at ht'
  have checked := renameInto hit j Δ keep
  simp only [blockHit,programRename,consTermRename,emptyTapeRename,sucRelabel,zRelabel] at checked
  have inBlock := blockMemberOfHit (k := 0) typeLeafSingleton (ty.relabel j) (key.relabel j)
    one Fin.elim0 actual checked
  have cell := singletonCell one (ty.relabel j) actual
  obtain ⟨same⟩ := singletonKey one (ty.relabel j) (key.relabel j) cell inBlock
  obtain ⟨typed⟩ := ht'
  exact introduce (K.relabel j) (key.relabel j) (ty.relabel j) typed same

theorem exact_OpenCoverTypeLeavesOrigin : ExactOpenCoverTypeLeavesOrigin := by
  intro body α Γ out K key run hit
  have found := exact_OpenCartesianFoldOrigin (k := 0) typeLeafSingleton body α Γ K key out Fin.elim0 run hit
  apply cartesianCases (k := 0) typeLeafSingleton K key Fin.elim0 _ found
  intro β j Δ ty keep witness
  rw [originRename]
  rw [emptyTapeRename] at witness
  obtain ⟨witness⟩ := witness
  exact atType (K.relabel j) (key.relabel j) ty ⟨Derivation.conjunctionLeft witness⟩
    ⟨Derivation.conjunctionRight witness⟩

#print axioms exact_OpenCoverTypeLeavesOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOriginProof

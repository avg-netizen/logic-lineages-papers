module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedPairState
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnPrefixedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeOnCoverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersSnapshotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnAtPoolsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalControlGraphSupportProof (headTransport programRename)
open NumberedWindowInternalSparseDirectedFilter (pass)
open NumberedWindowInternalThinPrefixedRoundsTargets (prefixed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMinimumProof
open NumberedWindowInternalLiteralLeastOnMembersProof
open NumberedWindowInternalLiteralLeastOnPrefixedProof
open NumberedWindowInternalLiteralEdgeOnCoverProof
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse edgeRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinMembersClosureChecks (exact_MembersEdgeClosure)
open NumberedWindowInternalThinActualMembersSnapshotProof
open NumberedWindowInternalThinPackedPairState

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

@[expose] def seedOn (C : Program 3) (E : Program 4) (s : Settings) {α : Type}
    (ctx ty a va pa x : OTerm α) : Formula α :=
  leastOnGraph C E s ctx ty a x ⊓
    (unary (scratchVertices C s) va a ⊓ programGraph (membersAtSeedOn C E s) pa ![ctx,ty,a])

theorem seedOnRename (C : Program 3) (E : Program 4) (s : Settings) {α β : Type}
    (ctx ty a va pa x : OTerm α) (j : α → β) :
    (seedOn C E s ctx ty a va pa x).relabel j =
      seedOn C E s (ctx.relabel j) (ty.relabel j) (a.relabel j)
        (va.relabel j) (pa.relabel j) (x.relabel j) := by
  simp only [seedOn,conjunctionRename,leastOnRename,unaryRename,programRename,tripleInputsRename]

@[expose] def pairOn (C : Program 3) (E : Program 4) (s : Settings) {α : Type}
    (p : PairPlan α) : Formula α :=
  seedOn C E s p.ctx p.ty p.a p.va p.pa p.x ⊓
    (seedOn C E s p.ctx p.ty p.b p.vb p.pb p.y ⊓ acceptEdge E p.ctx p.ty p.a p.b)

theorem pairOnRename (C : Program 3) (E : Program 4) (s : Settings) {α β : Type}
    (p : PairPlan α) (j : α → β) :
    (pairOn C E s p).relabel j = pairOn C E s (p.map j) := by
  simp only [pairOn,PairPlan.map,conjunctionRename,seedOnRename,edgeRename]

private theorem crossSeeds (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (E : Program 4) (s : Settings) (reverses : CanReverse E) (p : PairPlan α)
    (data : Derivation B Γ (pairOn C E s p)) (same : Derivation B Γ (eqn p.va p.vb)) :
    Nonempty (Derivation B Γ (memberGraph p.pb p.a ⊓ memberGraph p.pa p.b)) := by
  let a := Derivation.conjunctionLeft data
  let b := Derivation.conjunctionLeft (Derivation.conjunctionRight data)
  let edge := Derivation.conjunctionRight (Derivation.conjunctionRight data)
  let ca := Derivation.conjunctionLeft (Derivation.conjunctionRight a)
  let cb := Derivation.conjunctionLeft (Derivation.conjunctionRight b)
  let pa := Derivation.conjunctionRight (Derivation.conjunctionRight a)
  let pb := Derivation.conjunctionRight (Derivation.conjunctionRight b)
  obtain ⟨reverse⟩ := reverses B α Γ p.ctx p.ty p.a p.b ⟨edge⟩
  have hasVA := exact_OpenLeastOnSeedOrigin C E s p.ctx p.ty p.a p.va p.pa p.x
    ⟨Derivation.conjunctionLeft a⟩ ⟨pa⟩ ⟨ca⟩
  have hasVB := exact_OpenLeastOnSeedOrigin C E s p.ctx p.ty p.b p.vb p.pb p.y
    ⟨Derivation.conjunctionLeft b⟩ ⟨pb⟩ ⟨cb⟩
  obtain ⟨aThere⟩ := headTransport scratchMember (suc z) p.va p.vb ![p.a] ⟨same⟩ hasVA
  obtain ⟨bThere⟩ := headTransport scratchMember (suc z) p.vb p.va ![p.b] ⟨symm same⟩ hasVB
  obtain ⟨mA⟩ := exact_OpenLeastOnActualMembers C E s p.ctx p.ty p.a p.va p.pa ⟨ca⟩ ⟨pa⟩
  obtain ⟨mB⟩ := exact_OpenLeastOnActualMembers C E s p.ctx p.ty p.b p.vb p.pb ⟨cb⟩ ⟨pb⟩
  obtain ⟨hasPA⟩ := exact_OpenLeastOnSeedRetained E p.va p.ctx p.ty p.a p.pa hasVA ⟨mA⟩
  obtain ⟨hasPB⟩ := exact_OpenLeastOnSeedRetained E p.vb p.ctx p.ty p.b p.pb hasVB ⟨mB⟩
  obtain ⟨forward⟩ := exact_MembersEdgeClosure bound exact_RetainedPredecessor strict
    E B α Γ p.va p.ctx p.ty p.a p.pa p.a p.b
  obtain ⟨backward⟩ := exact_MembersEdgeClosure bound exact_RetainedPredecessor strict
    E B α Γ p.vb p.ctx p.ty p.b p.pb p.b p.a
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationElimination backward (Derivation.conjunctionIntroduction mB
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction hasPB reverse) aThere)))
    (Derivation.implicationElimination forward (Derivation.conjunctionIntroduction mA
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction hasPA edge) bThere)))⟩

private theorem movePrefixed (E : Program 4) (u v ctx ty pool later : OTerm α)
    (same : Derivation B Γ (eqn u v)) (h : Derivation B Γ (prefixed E u ctx ty pool later)) :
    Nonempty (Derivation B Γ (prefixed E v ctx ty pool later)) := by
  obtain ⟨pass'⟩ := headTransport (pass E) later u v ![pool,ctx,ty] ⟨same⟩
    ⟨Derivation.conjunctionLeft h⟩
  exact ⟨Derivation.conjunctionIntroduction pass' (Derivation.conjunctionRight h)⟩

private theorem finals (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (E : Program 4) (s : Settings) (reverses : CanReverse E)
    (coverLaw : KeepsCover C s E) (p : PairPlan α)
    (fa fb la lb : OTerm α) :
    Derivation B Γ (pairOn C E s p) →
    Derivation B Γ (snapshot E p.va p.ctx p.ty p.a p.pa fa la) →
    Derivation B Γ (snapshot E p.vb p.ctx p.ty p.b p.pb fb lb) →
    Nonempty (Derivation B Γ (eqn p.x p.y)) := by
  intro data snapA snapB
  let a := Derivation.conjunctionLeft data
  let b := Derivation.conjunctionLeft (Derivation.conjunctionRight data)
  let edge := Derivation.conjunctionRight (Derivation.conjunctionRight data)
  let ma := Derivation.conjunctionLeft a
  let mb := Derivation.conjunctionLeft b
  let va := Derivation.conjunctionLeft (Derivation.conjunctionRight a)
  let vb := Derivation.conjunctionLeft (Derivation.conjunctionRight b)
  let pa := Derivation.conjunctionRight (Derivation.conjunctionRight a)
  let pb := Derivation.conjunctionRight (Derivation.conjunctionRight b)
  obtain ⟨same⟩ := coverLaw B α Γ p.ctx p.ty p.a p.b p.va p.vb ⟨edge⟩ ⟨va⟩ ⟨vb⟩
  obtain ⟨cross⟩ := crossSeeds bound strict C E s reverses p data same
  have ra := Derivation.conjunctionLeft (Derivation.conjunctionRight snapA)
  have rb := Derivation.conjunctionLeft (Derivation.conjunctionRight snapB)
  have fixA := Derivation.conjunctionRight (Derivation.conjunctionRight snapA)
  have fixB := Derivation.conjunctionRight (Derivation.conjunctionRight snapB)
  obtain ⟨fixB'⟩ := movePrefixed E p.vb p.va p.ctx p.ty p.pb lb (symm same) fixB
  obtain ⟨fixA'⟩ := movePrefixed E p.va p.vb p.ctx p.ty p.pa la same fixA
  exact exact_OpenLeastOnPrefixed C E s B α Γ p.ctx p.ty p.a p.b
    p.va p.vb p.pa p.pb fa fb la lb p.x p.y ma mb pa pb ra rb
    (Derivation.conjunctionLeft cross) (Derivation.conjunctionRight cross) fixB' fixA'

/-- Restore equality of genuine original packed least outputs using the
actual ordered members pools and their real computed length/fixed passes.
No round, pre-fixed pass or cross-seed assumption is supplied by caller. -/
theorem exact_OpenLeastOnAtPools (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (E : Program 4) (s : Settings) (reverses : CanReverse E)
    (coverLaw : KeepsCover C s E) (p : PairPlan α)
    (held : Nonempty (Derivation B Γ (pairOn C E s p))) :
    Nonempty (Derivation B Γ (eqn p.x p.y)) := by
  obtain ⟨data⟩ := held
  let a := Derivation.conjunctionLeft data
  have members := exact_OpenLeastOnActualMembers C E s p.ctx p.ty p.a p.va p.pa
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight a)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight a)⟩
  apply exact_OpenThinActualMembersSnapshot bound exact_RetainedPredecessor strict E
    p.va p.ctx p.ty p.a p.pa (eqn p.x p.y) members
  intro β j Δ fa la keep snapA
  rw [eqnRelabel]
  let q := p.map j
  have moved := renameInto ⟨data⟩ j Δ keep
  rw [pairOnRename] at moved
  obtain ⟨newData⟩ := moved
  let b := Derivation.conjunctionLeft (Derivation.conjunctionRight newData)
  have memberB := exact_OpenLeastOnActualMembers C E s q.ctx q.ty q.b q.vb q.pb
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight b)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight b)⟩
  apply exact_OpenThinActualMembersSnapshot bound exact_RetainedPredecessor strict E
    q.vb q.ctx q.ty q.b q.pb (eqn q.x q.y) memberB
  intro γ k Θ fb lb keepB snapB
  rw [eqnRelabel]
  have aa : Nonempty (Derivation B Δ (snapshot E q.va q.ctx q.ty q.a q.pa fa la)) := snapA
  have old := renameInto aa k Θ keepB
  rw [snapshotRename] at old
  have both := renameInto ⟨newData⟩ k Θ keepB
  rw [pairOnRename] at both
  obtain ⟨both⟩ := both
  obtain ⟨old⟩ := old
  obtain ⟨new⟩ := snapB
  exact finals bound strict C E s reverses coverLaw (q.map k) (fa.relabel k) fb (la.relabel k) lb both old new

#print axioms exact_OpenLeastOnAtPools
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnAtPoolsProof

module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedPairState
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersSnapshotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedPackedMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

import LogicLineages.PersistentMarking.NumberedWindowInternalThinGuardedEdgeCoverProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastAtPoolsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open NumberedWindowInternalSparseDirectedFilter (pass)
open NumberedWindowInternalThinPrefixedRoundsTargets (prefixed)
open NumberedWindowInternalThinGuardedEdgeCoverProof (exact_ThinGuardedEdgeCover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinMembersClosureChecks (exact_MembersEdgeClosure)
open NumberedWindowInternalThinPackedEdgeMutualSeedProof
open NumberedWindowInternalThinPrefixedPackedMinimumProof (exact_OriginalPackedMinimumFromPrefixed)
open NumberedWindowInternalThinActualMembersSnapshotProof
open NumberedWindowInternalThinPackedPairState

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem sameCover (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings)
    (p : PairPlan α) (data : Derivation B Γ (pairReport C (guardedExchange C s (pairedExchange base)) W s p)) :
    Nonempty (Derivation B Γ (eqn p.va p.vb)) := by
  obtain ⟨q⟩ := exact_ThinGuardedEdgeCover C s (pairedExchange base) W B α Γ p.ctx p.ty p.a p.b p.va p.vb
  let a := Derivation.conjunctionLeft data
  let b := Derivation.conjunctionLeft (Derivation.conjunctionRight data)
  let edge := Derivation.conjunctionRight (Derivation.conjunctionRight data)
  exact ⟨Derivation.implicationElimination q (Derivation.conjunctionIntroduction edge
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft (Derivation.conjunctionRight a))
      (Derivation.conjunctionLeft (Derivation.conjunctionRight b))))⟩

private theorem movePrefixed (E : Program 4) (u v ctx ty pool later : OTerm α)
    (same : Derivation B Γ (eqn u v)) (h : Derivation B Γ (prefixed E u ctx ty pool later)) :
    Nonempty (Derivation B Γ (prefixed E v ctx ty pool later)) := by
  obtain ⟨pass'⟩ := headTransport (pass E) later u v ![pool,ctx,ty] ⟨same⟩
    ⟨Derivation.conjunctionLeft h⟩
  exact ⟨Derivation.conjunctionIntroduction pass' (Derivation.conjunctionRight h)⟩

private theorem finals (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings) (p : PairPlan α)
    (fa fb la lb : OTerm α) :
    let X := guardedExchange C s (pairedExchange base)
    Derivation B Γ (pairReport C X W s p) →
    Derivation B Γ (snapshot (edge4 X W) p.va p.ctx p.ty p.a p.pa fa la) →
    Derivation B Γ (snapshot (edge4 X W) p.vb p.ctx p.ty p.b p.pb fb lb) →
    Nonempty (Derivation B Γ (eqn p.x p.y)) := by
  intro X data snapA snapB
  let a := Derivation.conjunctionLeft data
  let b := Derivation.conjunctionLeft (Derivation.conjunctionRight data)
  let edge := Derivation.conjunctionRight (Derivation.conjunctionRight data)
  let ma := Derivation.conjunctionLeft a
  let mb := Derivation.conjunctionLeft b
  let va := Derivation.conjunctionLeft (Derivation.conjunctionRight a)
  let vb := Derivation.conjunctionLeft (Derivation.conjunctionRight b)
  let pa := Derivation.conjunctionRight (Derivation.conjunctionRight a)
  let pb := Derivation.conjunctionRight (Derivation.conjunctionRight b)
  obtain ⟨cross⟩ := exact_OpenThinPairedMutualSeedPresence exact_MembersEdgeClosure bound
    exact_RetainedPredecessor strict C base W s p.ctx p.ty p.a p.b p.va p.vb p.pa p.pb p.x p.y
    ma mb va vb pa pb edge
  have ra := Derivation.conjunctionLeft (Derivation.conjunctionRight snapA)
  have rb := Derivation.conjunctionLeft (Derivation.conjunctionRight snapB)
  have fixA := Derivation.conjunctionRight (Derivation.conjunctionRight snapA)
  have fixB := Derivation.conjunctionRight (Derivation.conjunctionRight snapB)
  obtain ⟨same⟩ := sameCover C base W s p data
  obtain ⟨fixB'⟩ := movePrefixed (edge4 X W) p.vb p.va p.ctx p.ty p.pb lb (symm same) fixB
  obtain ⟨fixA'⟩ := movePrefixed (edge4 X W) p.va p.vb p.ctx p.ty p.pa la same fixA
  exact exact_OriginalPackedMinimumFromPrefixed C X W s B α Γ p.ctx p.ty p.a p.b
    p.va p.vb p.pa p.pb fa fb la lb p.x p.y ma mb pa pb ra rb
    (Derivation.conjunctionLeft cross) (Derivation.conjunctionRight cross) fixB' fixA'

/-- Restore equality of genuine original packed least outputs using the
actual ordered members pools and their real computed length/fixed passes.
No round, pre-fixed pass or cross-seed assumption is supplied by caller. -/
theorem exact_OpenThinPairedPackedLeastAtPools (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings) (p : PairPlan α)
    (held : Nonempty (Derivation B Γ (pairReport C (guardedExchange C s (pairedExchange base)) W s p))) :
    Nonempty (Derivation B Γ (eqn p.x p.y)) := by
  let X := guardedExchange C s (pairedExchange base)
  let E := edge4 X W
  obtain ⟨data⟩ := held
  let a := Derivation.conjunctionLeft data
  have members := exact_OpenActualMembersFromCover C X W s p.ctx p.ty p.a p.va p.pa
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight a)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight a)⟩
  apply exact_OpenThinActualMembersSnapshot bound exact_RetainedPredecessor strict E
    p.va p.ctx p.ty p.a p.pa (eqn p.x p.y) members
  intro β j Δ fa la keep snapA
  rw [eqnRelabel]
  let q := p.map j
  have moved := renameInto ⟨data⟩ j Δ keep
  rw [pairRename] at moved
  obtain ⟨newData⟩ := moved
  let b := Derivation.conjunctionLeft (Derivation.conjunctionRight newData)
  have memberB := exact_OpenActualMembersFromCover C X W s q.ctx q.ty q.b q.vb q.pb
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
  rw [pairRename] at both
  obtain ⟨both⟩ := both
  obtain ⟨old⟩ := old
  obtain ⟨new⟩ := snapB
  exact finals bound strict C base W s (q.map k) (fa.relabel k) fb (la.relabel k) lb both old new

#print axioms exact_OpenThinPairedPackedLeastAtPools
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedPackedLeastAtPoolsProof

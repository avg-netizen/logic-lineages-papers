module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundStabilityTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundStabilityChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalScratchInclusionThinProof (included)
open NumberedWindowInternalScratchInclusionThinProof (includedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph seenWitness witnessRow)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessUnfold witnessBinder scanRename)
open NumberedWindowInternalSparseScanWitnessChecks (exact_WitnessRowAcceptance exact_OpenScanWitnessEquivalence)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalSparseFilterCompletenessChecks (exact_ScannedMemberRetention)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenRoundSuccessor)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalThinRoundStabilityTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem transport (E : Program 4) (left right ctx ty k : OTerm α)
    (inc : Nonempty (Derivation body Γ (included left right)))
    (witness : Derivation body Γ (seenWitness E left ctx ty k)) :
    Nonempty (Derivation body Γ (scanGraph E right ctx ty k)) := by
  rw [witnessUnfold] at witness
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Θ := witnessBinder E left ctx ty k :: Γ.map weaken
  have i := renameInto inc j Θ (fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩))
  rw [includedRename] at i
  have row : Derivation body Θ (witnessRow E (left.relabel j) (ctx.relabel j) (ty.relabel j) w (k.relabel j)) :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨onRight⟩ := NumberedWindowInternalScratchInclusionThinProof.eliminate (left.relabel j) (right.relabel j) w i
    ⟨Derivation.conjunctionLeft row⟩
  obtain ⟨accept⟩ := exact_WitnessRowAcceptance E body _ Θ (right.relabel j) (ctx.relabel j) (ty.relabel j) w (k.relabel j)
  have result := Derivation.implicationElimination accept
    (Derivation.conjunctionIntroduction onRight (Derivation.conjunctionRight row))
  have final : Derivation body Θ (weaken (scanGraph E right ctx ty k)) := by
    change Derivation body Θ ((scanGraph E right ctx ty k).relabel j)
    rwa [scanRename]
  exact ⟨Derivation.existentialElimination witness final⟩

theorem exact_ScanMonotonicity : ExactScanMonotonicity := by
  intro E body α Γ left right ctx ty k
  let A := included left right ⊓ scanGraph E left ctx ty k
  have h : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨both⟩ := exact_OpenScanWitnessEquivalence E body α (A :: Γ) left ctx ty k
  have row := Derivation.implicationElimination (Derivation.conjunctionLeft both) (Derivation.conjunctionRight h)
  obtain ⟨result⟩ := transport E left right ctx ty k ⟨Derivation.conjunctionLeft h⟩ row
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_PassMonotonicity : ExactPassMonotonicity := by
  intro paid E body α Γ vertices left right ctx ty a b
  let runs := passGraph E a vertices left ctx ty ⊓ passGraph E b vertices right ctx ty
  let A := included left right ⊓ runs
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have rr := Derivation.conjunctionRight h
  have grow : Nonempty (Derivation body Δ (included a b)) := by
    apply NumberedWindowInternalScratchInclusionThinProof.introduce
    intro β j Θ k keep hit
    have i := renameInto ⟨Derivation.conjunctionLeft h⟩ j Θ keep
    have l := renameInto ⟨Derivation.conjunctionLeft rr⟩ j Θ keep
    have r := renameInto ⟨Derivation.conjunctionRight rr⟩ j Θ keep
    rw [includedRename] at i
    rw [passRename] at l r
    obtain ⟨l⟩ := l
    obtain ⟨r⟩ := r
    obtain ⟨hit⟩ := hit
    have m : Derivation body Θ (memberGraph (a.relabel j) k) := hit
    have given := Derivation.conjunctionIntroduction l m
    obtain ⟨origin⟩ := exact_DirectedPassInclusion E body β Θ (a.relabel j) (vertices.relabel j)
      (left.relabel j) (ctx.relabel j) (ty.relabel j) k
    obtain ⟨prior⟩ := paid E body β Θ (vertices.relabel j) (left.relabel j) (ctx.relabel j)
      (ty.relabel j) (a.relabel j) k
    obtain ⟨test⟩ := transport E (left.relabel j) (right.relabel j) (ctx.relabel j) (ty.relabel j) k i
      (Derivation.implicationElimination prior given)
    obtain ⟨insert⟩ := exact_ScannedMemberRetention E body β Θ (b.relabel j) (vertices.relabel j)
      (right.relabel j) (ctx.relabel j) (ty.relabel j) k
    exact ⟨Derivation.implicationElimination insert (Derivation.conjunctionIntroduction r
      (Derivation.conjunctionIntroduction (Derivation.implicationElimination origin given) test))⟩
  obtain ⟨grow⟩ := grow
  exact ⟨Derivation.implicationIntroduction grow⟩

theorem exact_StableNext : ExactStableNext := by
  intro paid E body α Γ vertices ctx ty seed fuel a b c
  let runs := roundGraph E a fuel vertices ctx ty seed ⊓
    (roundGraph E b (suc fuel) vertices ctx ty seed ⊓ roundGraph E c (suc (suc fuel)) vertices ctx ty seed)
  let A := runs ⊓ included b a
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have stages := Derivation.conjunctionLeft h
  have bRun := Derivation.conjunctionLeft (Derivation.conjunctionRight stages)
  obtain ⟨one⟩ := exact_OpenRoundSuccessor E body α Δ b fuel vertices ctx ty seed a
  obtain ⟨two⟩ := exact_OpenRoundSuccessor E body α Δ c (suc fuel) vertices ctx ty seed b
  have pb := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination one (Derivation.conjunctionLeft stages))) bRun
  have pc := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination two bRun)) (Derivation.conjunctionRight (Derivation.conjunctionRight stages))
  obtain ⟨rule⟩ := exact_PassMonotonicity paid E body α Δ vertices b a ctx ty c b
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight h) (Derivation.conjunctionIntroduction pc pb)))⟩

#print axioms exact_ScanMonotonicity
#print axioms exact_PassMonotonicity
#print axioms exact_StableNext
end LogicLineages.PersistentMarking.NumberedWindowInternalThinRoundStabilityChecks

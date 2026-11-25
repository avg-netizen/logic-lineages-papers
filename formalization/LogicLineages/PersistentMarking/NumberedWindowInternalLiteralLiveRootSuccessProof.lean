module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLiveRootSuccessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename headTransport outputTransport valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem noZeroFlag {n : Nat} (q : Program n) (k f : OTerm α) (xs : Fin n → OTerm α)
    (goal : Formula α)
    (known : D B Γ (programGraph (emitState (constantZero n) q) (stateTerm (suc k) f) xs)) :
    D B Γ goal := by
  apply programCases q xs goal
  intro β j Δ v keep output
  let ts := fun i => (xs i).relabel j
  let k' := k.relabel j
  let f' := f.relabel j
  have held := renameInto known j Δ keep
  simp only [programRename,stateRename,sucRelabel] at held
  have made := emitGraph (constantZero n) q z v ts (constantZeroValue ts) output
  have eq := valueUnique (emitState (constantZero n) q) (stateTerm (suc k') f') (stateTerm z v)
    ts held made
  have read := headTransport cellHead (suc k') (stateTerm (suc k') f') (stateTerm z v) ![]
    eq (headRead (suc k') f')
  obtain ⟨bad⟩ := valueUnique cellHead (suc k') z ![stateTerm z v] read (headRead z v)
  exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩

private theorem recoverRootFlag {n : Nat} (p : Program n) (k f : OTerm α) (xs : Fin n → OTerm α)
    (known : D B Γ (programGraph (emitState p (constantZero n)) (stateTerm (suc k) f) xs)) :
    D B Γ (programGraph p (suc k) xs) := by
  apply programCases p xs (programGraph p (suc k) xs)
  intro β j Δ flag keep output
  let ts := fun i => (xs i).relabel j
  let k' := k.relabel j
  let f' := f.relabel j
  rw [programRename,sucRelabel]
  have held := renameInto known j Δ keep
  simp only [programRename,stateRename,sucRelabel] at held
  have made := emitGraph p (constantZero n) flag z ts output (constantZeroValue ts)
  have eq := valueUnique (emitState p (constantZero n)) (stateTerm flag z) (stateTerm (suc k') f')
    ts made held
  have read := headTransport cellHead flag (stateTerm flag z) (stateTerm (suc k') f') ![]
    eq (headRead flag z)
  have same := valueUnique cellHead flag (suc k') ![stateTerm (suc k') f'] read (headRead (suc k') f')
  exact outputTransport p flag (suc k') ts same output

/-- An arbitrary live tick that emits a nonzero flag comes from the
actual root callback on that exact tape. Neither zero-flag contextual
emitter can produce this result. This theorem does not assume a
syntactic root wrapper or identify the original tape with a numeral. -/
theorem exact_OpenLiveRootSuccess (p other : Program 3) (k f : OTerm α)
    (xs : Fin 3 → OTerm α)
    (known : D B Γ (programGraph (liveTick p other) (stateTerm (suc k) f) xs)) :
    D B Γ (programGraph (rootCall p) (suc k) xs) := by
  let fallback := emitState (constantZero 3) other
  let rooted := emitState (rootCall p) (constantZero 3)
  let inner := branch rootTest fallback rooted
  let ctx := emitState (constantZero 3) chosenFrame
  let goal := programGraph (rootCall p) (suc k) xs
  apply optionGraphCases tagFiveTest xs goal
  · intro β j Δ keep guard
    let ts := fun i => (xs i).relabel j
    let k' := k.relabel j
    let f' := f.relabel j
    have held := renameInto known j Δ keep
    simp only [programRename,stateRename,sucRelabel] at held
    have one := zeroBranchElim tagFiveTest inner ctx (stateTerm (suc k') f') ts guard held
    change D B Δ ((programGraph (rootCall p) (suc k) xs).relabel j)
    rw [programRename,sucRelabel]
    apply optionGraphCases rootTest ts (programGraph (rootCall p) (suc k') ts)
    · intro γ l Ω stay absent
      have nested := renameInto one l Ω stay
      simp only [programRename,stateRename,sucRelabel] at nested
      have bad := zeroBranchElim rootTest fallback rooted _ _ absent nested
      exact noZeroFlag other _ _ _ _ bad
    · intro γ l Ω pred stay present
      rw [programRename,sucRelabel]
      have nested := renameInto one l Ω stay
      simp only [programRename,stateRename,sucRelabel] at nested
      have active := successorBranchElim rootTest fallback rooted _ pred _ present nested
      exact recoverRootFlag (rootCall p) _ _ _ active
  · intro β j Δ pred keep guard
    let ts := fun i => (xs i).relabel j
    let k' := k.relabel j
    let f' := f.relabel j
    have held := renameInto known j Δ keep
    simp only [programRename,stateRename,sucRelabel] at held
    have bad := successorBranchElim tagFiveTest inner ctx (stateTerm (suc k') f') pred ts guard held
    exact noZeroFlag chosenFrame k' f' ts _ bad

#print axioms exact_OpenLiveRootSuccess
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLiveRootSuccessProof

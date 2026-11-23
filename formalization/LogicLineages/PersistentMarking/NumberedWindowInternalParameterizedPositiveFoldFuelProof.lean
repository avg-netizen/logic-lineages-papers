module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldIterationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSparseFieldCell (chosenCell)
open NumberedWindowInternalSparseFieldParserRawPairProof (tailBound)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (codeOfCell emptyUnpack missingUnpack splitUnpack)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState decodeState)
open NumberedWindowInternalSparsePositiveFoldTargets (encodeScratch)
open NumberedWindowInternalSparsePositiveFoldIterationProof (repeatStates repeatHead repeatStable)

/-- Read the actual ordered certificate using the original unpacker.
A is executed at each real head, even when its physical state is zero.
Neither malformed lists nor absent output states are converted into hits. -/
def foldPhysical (A : Program 4) (c ty start cert : Nat) : Option Nat := do
  let hops ← unpack cert
  hops.foldl (fun current hop => decodeState (evalPhysicalAdvance A c ty (encodeState current) hop))
    (decodeState start)

private theorem stateRound (n : Nat) : encodeState (decodeState n) = n := by cases n <;> rfl
private theorem optionRound (o : Option Nat) : decodeState (encodeState o) = o := by cases o <;> rfl

private theorem foldNil (A : Program 4) (c ty start : Nat) :
    foldPhysical A c ty start 0 = decodeState start := by
  simp only [foldPhysical,emptyUnpack,Option.bind_eq_bind,Option.bind_some,List.foldl_nil]

private theorem foldMissing (A : Program 4) (c ty start cert : Nat)
    (positive : cert ≠ 0) (missing : chosenCell cert = none) :
    foldPhysical A c ty start cert = none := by
  simp only [foldPhysical,missingUnpack positive missing,Option.bind_eq_bind,Option.bind_none]

private theorem foldCons (A : Program 4) (c ty start cert hop tail : Nat)
    (found : chosenCell cert = some (hop,tail)) :
    foldPhysical A c ty start cert =
      foldPhysical A c ty (evalPhysicalAdvance A c ty start hop) tail := by
  unfold foldPhysical
  rw [splitUnpack found]
  cases got : unpack tail <;>
    simp only [got,Option.map_none,Option.map_some,Option.bind_eq_bind,
      Option.bind_none,Option.bind_some,List.foldl_cons,optionRound,stateRound]

private theorem stable (A : Program 4) (c ty start fuel : Nat) :
    repeatStates (nextPhysicalState A c ty) fuel (0,start) = (0,start) :=
  repeatStable (nextPhysicalState A c ty) (0,start) (by simp [nextPhysicalState]) fuel

theorem exact_ParameterizedRepeatDecoded (A : Program 4) (c ty cert fuel start : Nat)
    (bound : cert ≤ fuel) :
    repeatStates (nextPhysicalState A c ty) fuel (cert,start) =
      (0,encodeState (foldPhysical A c ty start cert)) := by
  induction cert using Nat.strongRecOn generalizing fuel start with
  | ind cert ih =>
    cases cert with
    | zero => rw [stable,foldNil,stateRound]
    | succ n =>
      cases fuel with
      | zero => exact False.elim (Nat.not_succ_le_zero n bound)
      | succ k =>
        rw [repeatHead]
        cases found : chosenCell (n+1) with
        | none =>
          have now : nextPhysicalState A c ty (n+1,start) = (0,0) := by
            simp [nextPhysicalState,found]
          rw [now,stable,foldMissing A c ty start (n+1) (Nat.succ_ne_zero n) found] <;> rfl
        | some both =>
          obtain ⟨hop,tail⟩ := both
          have pred : n = pair hop tail := Nat.succ.inj (codeOfCell found)
          have lower : tail ≤ n := by rw [pred]; exact tailBound hop tail
          have enough : tail ≤ k := Nat.le_trans lower (Nat.le_of_succ_le_succ bound)
          let next := evalPhysicalAdvance A c ty start hop
          have now : nextPhysicalState A c ty (n+1,start) = (tail,next) := by
            simp [nextPhysicalState,found,next]
          rw [now,ih tail (Nat.lt_succ_of_le lower) k next enough,foldCons A c ty start (n+1) hop tail found]

theorem exact_ParameterizedFuelDecoded (A : Program 4) (c ty start cert fuel : Nat)
    (bound : cert ≤ fuel) :
    evaluate (iterateAt A) (fuel ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ cert ::ᵥ nil) =
      encodeScratch 0 (encodeState (foldPhysical A c ty start cert)) := by
  rw [exact_ParameterizedIterationValue,exact_ParameterizedRepeatDecoded A c ty cert fuel start bound]

#print axioms exact_ParameterizedRepeatDecoded
#print axioms exact_ParameterizedFuelDecoded

end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFold

module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericPartitionsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericScanProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryRawNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowDirectAlgorithm (direct directLists readWitness)
open NumberedWindowInternalSparsePathEnvelope (field run)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne vectorTwo vectorThree)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt rawTriple)
open NumberedWindowInternalDirectWitnessEnvelope (exactRawTriple)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit boundaryRaw expected)
open NumberedWindowInternalDirectBoundaryRawNumericProof (exact_NumericRawGuards)
open NumberedWindowInternalDirectSourcePartitionRawTargets (rawSourceCheck observePartition)
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectCoreTargets
open NumberedWindowInternalDirectCoreNumericTargets
open NumberedWindowInternalDirectCoreNumericSupportProof (conjunctionBit decideToNatOne)
open NumberedWindowInternalDirectCoreNumericPartitionsProof (exact_NumericSourceObserver exact_NumericTargetObserver)
open NumberedWindowInternalDirectCoreNumericScanProof (exact_NumericInsertionObserver)

private theorem routeThree (p : Program 3) (i j k : Fin 5) (xs : List.Vector Nat 5) :
    evaluate (route p ![i,j,k]) xs = evaluate p (xs.get i ::ᵥ xs.get j ::ᵥ xs.get k ::ᵥ nil) := by
  change evaluate p (ofFn (fun b : Fin 3 => xs.get (![i,j,k] b))) = _
  rw [vectorThree] <;> rfl

private theorem routeTwo (p : Program 2) (i j : Fin 5) (xs : List.Vector Nat 5) :
    evaluate (route p ![i,j]) xs = evaluate p (xs.get i ::ᵥ xs.get j ::ᵥ nil) := by
  change evaluate p (ofFn (fun b : Fin 2 => xs.get (![i,j] b))) = _
  rw [vectorTwo] <;> rfl

private theorem boundaryAtValue (scalar : Program 1) (s t k r a : Nat) :
    evaluate (boundaryAt scalar) (s ::ᵥ t ::ᵥ k ::ᵥ r ::ᵥ a ::ᵥ nil) =
      evaluate (boundaryRaw scalar) (s ::ᵥ t ::ᵥ r ::ᵥ nil) :=
  routeThree (boundaryRaw scalar) 0 1 3 _

private theorem sourceAtValue (count : Program 2) (s t k r a : Nat) :
    evaluate (sourceAt count) (s ::ᵥ t ::ᵥ k ::ᵥ r ::ᵥ a ::ᵥ nil) =
      evaluate (rawSourceCheck (observePartition count)) (s ::ᵥ k ::ᵥ r ::ᵥ nil) :=
  routeThree (rawSourceCheck (observePartition count)) 0 2 3 _

private theorem targetAtValue (count : Program 2) (s t k r a : Nat) :
    evaluate (targetAt count) (s ::ᵥ t ::ᵥ k ::ᵥ r ::ᵥ a ::ᵥ nil) =
      evaluate (rawTargetCheck count) (t ::ᵥ k ::ᵥ a ::ᵥ nil) :=
  routeThree (rawTargetCheck count) 1 2 4 _

private theorem scanAtValue (r : Program 3) (s t k p a : Nat) :
    evaluate (scanAt r) (s ::ᵥ t ::ᵥ k ::ᵥ p ::ᵥ a ::ᵥ nil) =
      evaluate (scan r) (a ::ᵥ p ::ᵥ nil) :=
  routeTwo (scan r) 4 3 _

/-- Actual potential decoding, before imposing the certificate's physical tag-5 guard. -/
private def listsAt (scalarTest : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (s t k r a : Nat) : Bool :=
  match unpack s, unpack t, unpack k, unpack r, actualEntries a with
  | some src,some dst,some keep,some rem,some entries =>
      directLists scalarTest positive src dst (keep,rem,entries)
  | _,_,_,_,_ => false

private theorem coreValue (scalar : Program 1) (r : Program 3) (count : Program 2)
    (scalarTest : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (sf : ScalarFit scalar scalarTest) (pf : PositiveFit r positive) (cf : CountFit count)
    (s t k rem a : Nat) :
    evaluate (core scalar r count) (s ::ᵥ t ::ᵥ k ::ᵥ rem ::ᵥ a ::ᵥ nil) =
      (listsAt scalarTest positive s t k rem a).toNat := by
  simp only [core,conjunctionBit,decideToNatOne,boundaryAtValue,sourceAtValue,targetAtValue,scanAtValue,
    exact_NumericRawGuards scalar scalarTest sf,exact_NumericSourceObserver count cf,
    exact_NumericTargetObserver count cf]
  cases hs : unpack s
  · simp [hs,expected,partition,listsAt]
  rename_i src
  cases ht : unpack t
  · simp [hs,ht,expected,partition,listsAt]
  rename_i dst
  cases hk : unpack k
  · simp [hs,ht,hk,expected,partition,listsAt]
  rename_i keep
  cases hr : unpack rem
  · simp [hs,ht,hk,hr,expected,partition,listsAt]
  rename_i removed
  rw [exact_NumericInsertionObserver r positive pf a rem removed hr,decideToNatOne]
  cases ha : actualEntries a
  · simp [hs,ht,hk,hr,ha,expected,partition,listsAt]
  rename_i added
  simp [hs,ht,hk,hr,ha,expected,partition,listsAt,directLists,entryOK,Option.any,
    Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
  have rowOrder : (fun e : NumberedWindowDirectAlgorithm.Entry =>
      positive e.2.1 e.2.2 e.1 && decide (e.2.1 ∈ removed)) = entryOK positive removed := by
    funext e
    exact Bool.and_comm _ _
  rw [rowOrder, Bool.and_comm (added.all (entryOK positive removed))
    (decide (dst.Perm (keep ++ added.map Prod.fst)))]

private theorem fiveValues (f : Fin 5 → Nat) :
    ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ f 4 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun m => Fin.cases ?_ (fun u => Fin.elim0 u) m) l) k) j) i <;> simp <;> rfl

private theorem onCertValue (p : Program 1) (s w t : Nat) :
    evaluate (onCert p) (s ::ᵥ w ::ᵥ t ::ᵥ nil) = run p w := by
  change evaluate (.composition p (Fin.cons (.projection 1) Fin.elim0)) _ = _
  rw [compositeOne]
  rfl

private theorem witnessValue (p : Program 5) (s w t : Nat) :
    evaluate (.composition p witnessAt) (s ::ᵥ w ::ᵥ t ::ᵥ nil) =
      evaluate p (s ::ᵥ t ::ᵥ run (field 0) w ::ᵥ run (field 1) w ::ᵥ run (field 2) w ::ᵥ nil) := by
  let xs := s ::ᵥ w ::ᵥ t ::ᵥ nil
  change evaluate p (ofFn (fun i : Fin 5 => evaluate (witnessAt i) xs)) = _
  rw [fiveValues]
  change evaluate p (s ::ᵥ t ::ᵥ evaluate (onCert (field 0)) xs ::ᵥ
    evaluate (onCert (field 1)) xs ::ᵥ evaluate (onCert (field 2)) xs ::ᵥ nil) = _
  simp only [xs,onCertValue]

private theorem readWitnessAt (w : Nat) :
    readWitness w = (do
      let (k,r,a) ← rawTriple 5 w
      let kept ← unpack k
      let removed ← unpack r
      let added ← actualEntries a
      pure (kept,removed,added)) := by
  rw [exactRawTriple]
  unfold readWitness
  cases h : unpackNode w with
  | none => rfl
  | some p =>
    obtain ⟨tag,xs⟩ := p
    rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      rcases tag with _ | _ | _ | _ | _ | _ | tag <;> try rfl
    change (do
      let kept ← unpack a
      let removed ← unpack b
      let inputs ← unpack c
      let added ← NumberedWindowDirectAlgorithm.entries inputs
      pure (kept,removed,added)) = (do
      let kept ← unpack a
      let removed ← unpack b
      let added ← actualEntries c
      pure (kept,removed,added))
    unfold actualEntries
    cases ha : unpack a <;> cases hb : unpack b <;> cases hc : unpack c <;>
      simp [ha,hb,hc,Option.bind]

theorem exact_NumericDCore : ExactNumericDCore := by
  intro scalar r count scalarTest positive sf pf cf src cert dst
  simp only [dCore,conjunctionBit,onCertValue,witnessValue,coreValue scalar r count scalarTest positive sf pf cf,
    decideToNatOne]
  unfold direct
  rw [readWitnessAt]
  by_cases h : run (guardAt 5) cert = 1
  · have hb : decide (run (guardAt 5) cert = 1) = true := by simp [h]
    simp only [hb,Bool.true_and,rawTriple,h,if_true,Option.bind]
    generalize run (field 0) cert = k
    generalize run (field 1) cert = rem
    generalize run (field 2) cert = a
    cases hs : unpack src <;> cases ht : unpack dst <;> cases hk : unpack k <;>
      cases hr : unpack rem <;> cases ha : actualEntries a <;>
      simp [listsAt,hs,ht,hk,hr,ha]
  · simp [rawTriple,h]

#print axioms exact_NumericDCore
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericProof

module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawTargetNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree)
open NumberedWindowInternalSparsePositiveFoldStateEvaluationProof (vectorFive)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowDirectAlgorithm (Entry entries readEntry readWitness directLists direct)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalDirectCoreNumericTargets
open NumberedWindowInternalDirectCoreTargets
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit boundaryRaw)
open NumberedWindowInternalDirectBoundaryNumericProof (exact_DirectBoundaryRawNumeric)
open NumberedWindowInternalDirectRawSourceNumericProof (exact_RawSourcePartitionNumeric)
open NumberedWindowInternalDirectRawTargetNumericProof (exact_RawTargetPartitionNumeric)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (mapped)
open NumberedWindowInternalDirectInsertedScanNumericProof (exact_OriginalInsertedScanNumeric)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalDirectWitnessNumericProof (exact_TripleGuard exact_TripleFields)

private theorem bitAnd {n : Nat} (p q : Program n) (tape : List.Vector Nat n) (a b : Bool)
    (h : evaluate p tape = a.toNat) (k : evaluate q tape = b.toNat) :
    evaluate (conjunction p q) tape = (a && b).toNat := by
  rw [conjunctionEvaluation,h,k]
  cases a <;> cases b <;> rfl

private theorem onThree (p : Program 3) (i j k : Fin 5) (xs : List.Vector Nat 5) :
    evaluate (route p ![i,j,k]) xs = evaluate p (xs.get i ::ᵥ xs.get j ::ᵥ xs.get k ::ᵥ nil) := by
  unfold route
  rw [evaluate,vectorThree]
  rfl

private theorem onTwo (p : Program 2) (i j : Fin 5) (xs : List.Vector Nat 5) :
    evaluate (route p ![i,j]) xs = evaluate p (xs.get i ::ᵥ xs.get j ::ᵥ nil) := by
  unfold route
  rw [evaluate,vectorTwo]
  rfl

private def boundary (test : Nat → Bool) (s t r : Nat) :=
  NumberedWindowInternalDirectBoundaryGuardsTargets.expected test s t r

private def insertions (r : Program 3) (a d : Nat) :=
  (unpack a).any (fun rows => rows.all (NumberedWindowInternalDirectInsertedRowTargets.expected r d))

private def coreMeaning (test : Nat → Bool) (r : Program 3) (s t kept rem add : Nat) : Bool :=
  boundary test s t rem &&
    (partition (unpack s) (unpack kept) (unpack rem) &&
      (partition (unpack t) (unpack kept) ((unpack add).bind mapped) &&
        insertions r add rem))

private theorem coreNumeric (scalar : Program 1) (r : Program 3) (count : Program 2)
    (test : Nat → Bool) (fit : ScalarFit scalar test) (countFit : CountFit count)
    (s t k d a : Nat) :
    evaluate (core scalar r count) (s ::ᵥ t ::ᵥ k ::ᵥ d ::ᵥ a ::ᵥ nil) =
      (coreMeaning test r s t k d a).toNat := by
  let tape := s ::ᵥ t ::ᵥ k ::ᵥ d ::ᵥ a ::ᵥ nil
  let P := partition (unpack s) (unpack k) (unpack d)
  let Q := partition (unpack t) (unpack k) ((unpack a).bind mapped)
  have first : evaluate (boundaryAt scalar) tape = (boundary test s t d).toNat :=
    (onThree (boundaryRaw scalar) 0 1 3 tape).trans
      (exact_DirectBoundaryRawNumeric scalar test fit s t d)
  have src : evaluate (sourceAt count) tape = P.toNat :=
    (onThree _ 0 2 3 tape).trans (exact_RawSourcePartitionNumeric count countFit s k d)
  have dst : evaluate (targetAt count) tape = Q.toNat :=
    (onThree _ 1 2 4 tape).trans (exact_RawTargetPartitionNumeric count countFit t k a)
  have scan : evaluate (NumberedWindowInternalDirectCoreTargets.scanAt r) tape = (insertions r a d).toNat :=
    (onTwo (NumberedWindowInternalDirectInsertedScanTargets.scan r) 4 3 tape).trans
      (exact_OriginalInsertedScanNumeric r a d)
  exact bitAnd _ _ tape (boundary test s t d) _ first
    (bitAnd _ _ tape P _ src (bitAnd _ _ tape Q _ dst scan))

private theorem memBit (xs : List Nat) (x : Nat) :
    xs.any (fun a => a == x) = decide (x ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons,List.mem_cons,ih]
    by_cases eq : x = a
    · subst a
      simp
    · simp [eq,Ne.symm eq]

private theorem rowConversion (r : Program 3) (positive : Nat → Nat → Nat → Bool)
    (fit : PositiveFit r positive) (removed row : Nat) (rs : List Nat) (e : Entry)
    (decodedRemoved : unpack removed = some rs) (decodedRow : readEntry row = some e) :
    NumberedWindowInternalDirectInsertedRowTargets.expected r removed row = entryOK positive rs e := by
  obtain ⟨target,dom,cert⟩ := e
  unfold NumberedWindowInternalDirectInsertedRowTargets.expected entryOK
  rw [decodedRemoved,decodedRow]
  change (rs.any (fun x => x == dom) && decide (evaluate r (dom ::ᵥ cert ::ᵥ target ::ᵥ nil) = 1)) = _
  rw [memBit,fit dom cert target]
  cases positive dom cert target <;> simp

private theorem scanConversion (r : Program 3) (positive : Nat → Nat → Nat → Bool)
    (fit : PositiveFit r positive) (d : Nat) (rows : List Nat) (rs : List Nat) (es : List Entry)
    (removed : unpack d = some rs) (parsed : entries rows = some es) :
    rows.all (NumberedWindowInternalDirectInsertedRowTargets.expected r d) = es.all (entryOK positive rs) := by
  induction rows generalizing es with
  | nil =>
    have e : es = [] := (Option.some.inj parsed).symm
    subst es
    rfl
  | cons row rows ih =>
    change (do
      let x ← readEntry row
      let tail ← entries rows
      pure (x :: tail)) = some es at parsed
    cases yes : readEntry row with
    | none => rw [yes] at parsed; cases parsed
    | some x =>
      cases tail : entries rows with
      | none => rw [yes,tail] at parsed; cases parsed
      | some xs =>
        rw [yes,tail] at parsed
        have eq : x :: xs = es := Option.some.inj parsed
        subst es
        rw [List.all_cons,List.all_cons,rowConversion r positive fit d row rs x removed yes,ih xs tail]

private def decodedWitness (k d a : Nat) : Option NumberedWindowDirectAlgorithm.Witness := do
  let kept ← unpack k
  let removed ← unpack d
  let add ← (unpack a).bind entries
  pure (kept,removed,add)

private theorem fieldMeaning (test : Nat → Bool) (r : Program 3)
    (positive : Nat → Nat → Nat → Bool) (fit : PositiveFit r positive)
    (s t k d a : Nat) :
    coreMeaning test r s t k d a =
      match unpack s, decodedWitness k d a, unpack t with
      | some xs, some w, some ys => directLists test positive xs ys w
      | _,_,_ => false := by
  unfold coreMeaning boundary insertions decodedWitness partition
    NumberedWindowInternalDirectBoundaryGuardsTargets.expected
  cases hs : unpack s <;> cases ht : unpack t <;> cases hk : unpack k <;> cases hd : unpack d <;>
    cases ha : unpack a <;> try simp [Option.bind]
  rename_i xs ys kept rem rows
  have mappedDef : mapped rows = (entries rows).map (List.map Prod.fst) := rfl
  rw [mappedDef]
  cases he : entries rows with
  | none => simp
  | some es =>
    have scan := scanConversion r positive fit d rows rem es hd he
    simp only [Option.map_some] at *
    rw [scan]
    simp only [directLists,Bool.and_assoc]
    ac_rfl

private theorem chooseFields {w k d a : Nat} (h : unpackNode w = some (5,[k,d,a])) :
    readWitness w = decodedWitness k d a := by
  unfold readWitness decodedWitness
  rw [h]
  cases hk : unpack k <;> cases hd : unpack d <;> cases ha : unpack a <;>
    simp [Option.bind,hk,hd,ha]

private theorem invalidWitness (w : Nat)
    (no : ¬ ∃ k d a, unpackNode w = some (5,[k,d,a])) :
    readWitness w = none := by
  unfold readWitness
  cases t : unpackNode w with
  | none => rfl
  | some p =>
    obtain ⟨tag,rows⟩ := p
    rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
      rcases rows with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rs⟩⟩⟩⟩ <;> try rfl
    exact False.elim (no ⟨a,b,c,t⟩)

/-- The visibly installed Paper 16 direct checker, on every raw input
including malformed witnesses and duplicates, is the original algorithm
under the literal scalar/relation/observer calibrations. -/
theorem exact_OriginalDirectCoreNumeric : ExactNumericDCore := by
  intro scalar r count test positive fit pos countFit src wit dst
  let tape := src ::ᵥ wit ::ᵥ dst ::ᵥ nil
  change evaluate (dCore scalar r count) tape = _
  unfold dCore
  rw [conjunctionEvaluation]
  have g : evaluate (onCert (guardAt 5)) tape = run (guardAt 5) wit := by
    unfold onCert
    rw [evaluate,vectorOne]
    rfl
  rw [g]
  by_cases h : run (guardAt 5) wit = 1
  · obtain ⟨k,d,a,shape⟩ := (exact_TripleGuard 5 wit).mp h
    obtain ⟨keep,rem,add⟩ := exact_TripleFields shape
    have val (j : Nat) : evaluate (onCert (field j)) tape = run (field j) wit := by
      unfold onCert
      rw [evaluate,vectorOne]
      rfl
    have computed : evaluate (.composition (core scalar r count) witnessAt) tape =
        (coreMeaning test r src dst k d a).toNat := by
      rw [evaluate,vectorFive]
      change evaluate (core scalar r count) (src ::ᵥ dst ::ᵥ
        evaluate (onCert (field 0)) tape ::ᵥ evaluate (onCert (field 1)) tape ::ᵥ
        evaluate (onCert (field 2)) tape ::ᵥ nil) = _
      rw [val,val,val,keep,rem,add,coreNumeric scalar r count test fit countFit]
    rw [h,computed,fieldMeaning test r positive pos, direct,chooseFields shape]
    let b := match unpack src, decodedWitness k d a, unpack dst with
      | some xs, some w, some ys => directLists test positive xs ys w
      | _,_,_ => false
    change (if (1 : Nat) = 1 ∧ b.toNat = 1 then 1 else 0) = b.toNat
    cases b <;> rfl
  · have w := invalidWitness wit (fun e => h ((exact_TripleGuard 5 wit).mpr e))
    simp [h,direct,w]

#print axioms exact_OriginalDirectCoreNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreCalibrationProof

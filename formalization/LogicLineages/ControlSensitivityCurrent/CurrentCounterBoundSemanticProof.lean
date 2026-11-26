module
public import LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationProof
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentProof
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainProof
public import LogicLineages.OrdinalComparison.WWEncodedComparisonProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCounterBound

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open OriginalInput (Query context)
open ForwardTranslation SourceGroundComponentEnvironment

theorem ground_context (q : Query) : SourceMachineRawValuations.AllGround (context q) :=
  fun _ hσ => (List.mem_replicate.mp hσ).2

private theorem lookup (q : Query) (xs : List Nat) (hxs : xs.length = q.1)
    (c : OrdinalComponent (context q)) :
    (tupleEnvironment xs).getD (OrdinalSyntax.componentCode c) 0 = tupleRaw xs c := by
  have hl : (xs.map Nat.succ).length = (context q).length := by
    simp [context, hxs]
  have h := SourceGroundComponentEnvironment.Proof.typedLookup (context q) (xs.map Nat.succ)
    (ground_context q) hl c
  have hi : SourceTypedPorts.variableIndex c.2.1 < xs.length := by
    rw [hxs]
    have ht := SourceTypedPortsProof.typedVariableIndex.1 _ _ c.2.1
    simpa [context] using ht
  simpa [tupleEnvironment, tupleRaw, rawValuation, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi] using h

private theorem weak_note (a b : NONote) :
    rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) ≤ 1 ↔ a.1.repr ≤ b.1.repr := by
  obtain ⟨hlt, heq, hgt⟩ := rawComparisonOrdinalCorrect a b
  constructor
  · contrapose!
    intro h
    rw [hgt.mpr h]
    decide
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · rw [hlt.mpr h]; decide
    · rw [heq.mpr h]

private noncomputable def noteAt (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (q : Query) (xs : List Nat) (hxs : xs.length = q.1)
    (e : OrdinalExpression (context q)) : NONote :=
  (CurrentOrdinalEvaluation.calibration f hf _ OrdinalSyntax.componentCode e
    (tupleEnvironment xs) (tupleRaw xs) (lookup q xs hxs)).choose

private theorem noteAt_spec (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (q : Query) (xs : List Nat) (hxs : xs.length = q.1) (e : OrdinalExpression (context q)) :
    CurrentOrdinalEvaluation.evaluate f (tupleEnvironment xs) (OrdinalSyntax.typedCode e) =
      rawNoteEncode (noteAt f hf q xs hxs e).1 ∧
    (noteAt f hf q xs hxs e).1.repr =
      ParametricSourceSuccessor.denoteWith f (fun c => (tupleRaw xs c : Ordinal)) e :=
  (CurrentOrdinalEvaluation.calibration f hf _ OrdinalSyntax.componentCode e
    (tupleEnvironment xs) (tupleRaw xs) (lookup q xs hxs)).choose_spec

private theorem vector_notes (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (q : Query) (xs : List Nat) (hxs : xs.length = q.1) {m : Nat}
    (v : OrdinalVector (context q) m) :
    ∃ a : List NONote,
      evaluators f (tupleEnvironment xs) (OrdinalSyntax.vectorCode v) = normalCodes a ∧
      ∀ j, (a.getD j zeroNote).1.repr = coordinate f v (tupleRaw xs) j := by
  refine ⟨List.ofFn (fun j => noteAt f hf q xs hxs (v j)), ?_, ?_⟩
  · simp only [evaluators, OrdinalSyntax.vectorCode, normalCodes, List.map_ofFn,
      Function.comp_def, (noteAt_spec f hf q xs hxs _).1]
  · intro j
    by_cases hj : j < m+1
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj,
        Option.getD_some, coordinate, ordinalVectorAt]
      exact (noteAt_spec f hf q xs hxs _).2
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hj,
        Option.getD_none, coordinate, ordinalVectorAt, zeroNote,
        ParametricSourceSuccessor.denoteWith]
      rfl

private theorem note_compare (strict : Bool) (a b : List NONote) :
    compareNotes strict (normalCodes a) (normalCodes b) = true ↔
      (∀ j : Nat, (a.getD (j+1) zeroNote).1.repr ≤ (b.getD (j+1) zeroNote).1.repr) ∧
      if strict then (a.getD 0 zeroNote).1.repr < (b.getD 0 zeroNote).1.repr
      else (a.getD 0 zeroNote).1.repr ≤ (b.getD 0 zeroNote).1.repr := by
  have tail (a : List NONote) : (normalCodes a).tail = normalCodes a.tail := by
    cases a <;> rfl
  have at0 (a : List NONote) : (normalCodes a).getD 0 0 = rawNoteEncode (a.getD 0 zeroNote).1 :=
    List.getD_map a zeroNote (fun x => rawNoteEncode x.1)
  have atNext (a : List NONote) (j : Nat) : a.tail.getD j zeroNote = a.getD (j+1) zeroNote := by
    cases a <;> rfl
  unfold compareNotes
  rw [Bool.and_eq_true_iff, tail, tail, positiveComparisonSourceCorrect, at0, at0]
  simp only [positiveNoteAt, atNext]
  cases strict
  · simp only [Bool.false_eq_true, if_false, decide_eq_true_eq, weak_note]
  · simp only [if_true, decide_eq_true_eq, (rawComparisonOrdinalCorrect _ _).1]

private theorem compared_vectors (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (q : Query) (xs : List Nat) (hxs : xs.length = q.1) {m n : Nat}
    (a : OrdinalVector (context q) m) (b : OrdinalVector (context q) n) :
    compareNotes q.2.1 (evaluators f (tupleEnvironment xs) (OrdinalSyntax.vectorCode a))
      (evaluators f (tupleEnvironment xs) (OrdinalSyntax.vectorCode b)) = true ↔
    compareAt f q.2.1 a b (tupleRaw xs) := by
  obtain ⟨an, ea, va⟩ := vector_notes f hf q xs hxs a
  obtain ⟨bn, eb, vb⟩ := vector_notes f hf q xs hxs b
  rw [ea, eb, note_compare]
  simp only [va, vb, compareAt]

theorem pointCalibration : CurrentCounterBoundTargets.PointCalibration := by
  intro p f hf q xs hxs
  have literal := PolicyAssignmentStatementChecks.full.1 p (context q)
  have exactCode := PolicyAssignmentStatementChecks.full.2.1 p (context q)
  constructor
  · intro ht τ υ a b av bv ha hb hav hbv
    have ea := literal τ a
    have eb := literal υ b
    rw [ha, hav] at ea
    rw [hb, hbv] at eb
    unfold test assignments at ht
    dsimp only at ht
    rw [ea, eb] at ht
    exact (compared_vectors f hf q xs hxs av bv).mp ht
  · intro h
    unfold test assignments
    dsimp only
    cases ea : PolicyAssignment.assignmentCode p ((context q).map SyntaxCode.typeCode) q.2.2.1 with
    | none => rfl
    | some ac =>
      cases eb : PolicyAssignment.assignmentCode p ((context q).map SyntaxCode.typeCode) q.2.2.2 with
      | none => rfl
      | some bc =>
        obtain ⟨τ, a, av, ha, hav, rfl⟩ := (exactCode _ _).mp ea
        obtain ⟨υ, b, bv, hb, hbv, rfl⟩ := (exactCode _ _).mp eb
        exact (compared_vectors f hf q xs hxs av bv).mpr (h τ υ a b av bv ha hb hav hbv)

theorem all_tuples (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) :
    Good p f q ↔ ∀ xs : List Nat, xs.length = q.1 → Point p f q xs := by
  constructor
  · intro h xs _ τ υ a b av bv ha hb hav hbv
    exact h τ υ a b av bv ha hb hav hbv _ (fun c => by simp [tupleRaw])
  · intro h τ υ a b av bv ha hb hav hbv ρ hρ
    obtain ⟨xs, hlen, hx⟩ := groundPositiveTupleComplete (context q) (ground_context q) ρ hρ
    have ht := h xs (by simpa [context] using hlen) τ υ a b av bv ha hb hav hbv
    have he : (tupleRaw xs : OrdinalComponent (context q) → Nat) = ρ := funext hx
    rwa [he] at ht

end LogicLineages.ControlSensitivityCurrent.CurrentCounterBound

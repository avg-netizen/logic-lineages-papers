module
public import LogicLineages.PermittedControl.RawProperClauseTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawClosedPrimitiveProof
import LogicLineages.OrdinalComparison.RawComparisonProof
import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramProof
import LogicLineages.OrdinalComparison.RawNotationCode
import Mathlib.Computability.Primrec.List

public section
namespace LogicLineages.PermittedControl.RawProperClause
open OrdinalComparison (rawNoteEncode rawNoteDecode rawNoteDecodeEncode rawComparisonCode
  rawComparisonOrdinalCorrect rawComparisonPrimitiveRecursive encodedOrdinalFiniteRemainder)
open PreparedProjection (LowerOperand LowerOperandCode)
open FieldComparison (ValueField ProperField LongFieldCode longFieldCode)
open MixedSameRankResidue (WeightedCode properOperand encodeWeighted)
open SignedRowGuardedTest (Test)
open HeterogeneousSignedMatrixSlice (encodeTest)
open OriginalPrintedTerminalBitClauses (BitRow)
open OriginalPrintedLiteralRowBridge (properClauses AdmittedOperandRow AdmittedLiteralClause)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily)
open ActualBitFamilyRawClosed (admittedCode)

/-! ## Calibration -/

theorem codePos (o : ONote) : 0 < rawNoteEncode o ↔ o.repr ≠ 0 := by
  cases o with
  | zero =>
    constructor
    · intro h
      exact absurd h (Nat.lt_irrefl 0)
    · intro h
      exact (h rfl).elim
  | oadd e n a =>
    have h : ONote.repr 0 < ONote.repr (ONote.oadd e n a) := ONote.lt_def.mp (ONote.oadd_pos e n a)
    rw [ONote.repr_zero] at h
    constructor
    · intro _
      exact h.ne'
    · intro _
      exact Nat.succ_pos _

theorem exactLimitCode : ExactLimitCode := by
  intro eta
  have hc := OrdinalComparison.OrdinalSuccessorProgram.classification eta
  have hp := codePos eta.1
  have hb : Order.IsSuccLimit eta.1.repr → eta.1.repr ≠ 0 := fun h => by
    have hne := h.ne_bot
    rwa [Ordinal.bot_eq_zero] at hne
  simp only [limitCode,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨pos,rem⟩
    rcases hc.mp rem with z | l
    · exact absurd z (hp.mp pos)
    · exact l
  · intro l
    exact ⟨hp.mpr (hb l),hc.mpr (Or.inr l)⟩

theorem codeZero (mu : NONote) : rawNoteEncode mu.1 = 0 ↔ mu.1.repr = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos := (codePos mu.1).mpr hne
    omega
  · intro h
    by_contra hne
    exact (codePos mu.1).mp (Nat.pos_of_ne_zero hne) h

theorem exactProperFieldCode : ExactProperFieldCode := by
  intro F
  cases F with
  | iterate a => exact iff_of_true rfl trivial
  | entry a lam mu =>
    have hl := exactLimitCode lam
    have hm := exactLimitCode mu
    have hz := codeZero mu
    have hlt : rawComparisonCode (rawNoteEncode mu.1) (rawNoteEncode lam.1) = 0 ↔
        mu.1.repr < lam.1.repr := (rawComparisonOrdinalCorrect mu lam).1
    have key : properFieldCode (longFieldCode (.entry a lam mu)) =
        ((limitCode (rawNoteEncode lam.1) &&
            (decide (rawNoteEncode mu.1 = 0) || limitCode (rawNoteEncode mu.1))) &&
          decide (rawComparisonCode (rawNoteEncode mu.1) (rawNoteEncode lam.1) = 0)) := rfl
    rw [key]
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
    rw [hl,hm,hz,hlt]
    exact and_assoc

theorem exactProperOperandCode : ExactProperOperandCode := by
  intro op
  cases op with
  | coordinate rank => exact iff_of_true rfl trivial
  | ordinary rank F =>
    first
      | exact exactProperFieldCode F
      | (show properFieldCode (longFieldCode F) = true ↔ ProperField F
         exact exactProperFieldCode F)
  | count rank lam mu =>
    first
      | exact exactProperFieldCode (.entry 0 lam mu)
      | (show properFieldCode (longFieldCode (.entry 0 lam mu)) = true ↔ ProperField (.entry 0 lam mu)
         exact exactProperFieldCode (.entry 0 lam mu))

theorem exactAdmittedTestCode : ExactAdmittedTestCode := by
  intro t
  cases t with
  | equalZero => exact iff_of_true rfl trivial
  | nonnegative => exact iff_of_true rfl trivial
  | positive => exact iff_of_true rfl trivial
  | congruence m =>
    first
      | (change ((decide (3 < 3) && decide (m = 0)) || (decide (3 = 3) && decide (0 < m))) = true ↔ 0 < m
         simp)
      | simp [admittedCode,encodeTest,SignedRowGuardedTest.Test.Admitted]

theorem exactAdmittedRowCode : ExactAdmittedRowCode := by
  intro row
  change (admittedCode (encodeTest row.1.1) &&
      (row.1.2.2.map encodeWeighted).all (fun t : WeightedCode => properOperandCode t.2)) = true ↔
    row.1.1.Admitted ∧ ∀ t ∈ row.1.2.2, properOperand t.2
  rw [Bool.and_eq_true,List.all_eq_true,exactAdmittedTestCode row.1.1]
  apply and_congr Iff.rfl
  constructor
  · intro h t used
    exact (exactProperOperandCode t.2).mp (h (encodeWeighted t) (List.mem_map.mpr ⟨t,used,rfl⟩))
  · intro h c used
    obtain ⟨t,member,rfl⟩ := List.mem_map.mp used
    exact (exactProperOperandCode t.2).mpr (h t member)

theorem exactAdmittedClauseCode : ExactAdmittedClauseCode := by
  intro rows
  change (rows.map encodeBitRow).all admittedRowCode = true ↔ ∀ row ∈ rows, AdmittedOperandRow row
  rw [List.all_eq_true]
  constructor
  · intro h row used
    exact (exactAdmittedRowCode row).mp (h (encodeBitRow row) (List.mem_map.mpr ⟨row,used,rfl⟩))
  · intro h c used
    obtain ⟨row,member,rfl⟩ := List.mem_map.mp used
    exact (exactAdmittedRowCode row).mpr (h row member)

theorem exactRawProperClauses : ExactRawProperClauses := by
  intro family
  change (family.map (List.map encodeBitRow)).filter admittedClauseCode =
    (family.filter (fun rows => @decide (AdmittedLiteralClause rows) (Classical.propDecidable _))).map
      (List.map encodeBitRow)
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro rows _
  apply Bool.eq_iff_iff.mpr
  change admittedClauseCode (rows.map encodeBitRow) = true ↔ _
  rw [exactAdmittedClauseCode rows]
  constructor
  · intro h
    exact @decide_eq_true _ (Classical.propDecidable _) h
  · intro h
    exact @of_decide_eq_true _ (Classical.propDecidable _) h

/-! ## Injectivity of the operand code -/

private theorem noteInj (a b : NONote) (h : rawNoteEncode a.1 = rawNoteEncode b.1) : a = b := by
  have e₁ : rawNoteDecode (rawNoteEncode a.1) = a.1 := rawNoteDecodeEncode a.1
  have e₂ : rawNoteDecode (rawNoteEncode b.1) = b.1 := rawNoteDecodeEncode b.1
  rw [h] at e₁
  exact Subtype.ext (e₁.symm.trans e₂)

private theorem fieldInj : ∀ (F G : ValueField), longFieldCode F = longFieldCode G → F = G
  | .iterate a, .iterate b, h => by
    have e : a = b := congrArg (fun c : LongFieldCode => c.2.1) h
    rw [e]
  | .iterate _, .entry _ _ _, h => by
    have e : (0 : Nat) = 1 := congrArg (fun c : LongFieldCode => c.1) h
    exact absurd e (by decide)
  | .entry _ _ _, .iterate _, h => by
    have e : (1 : Nat) = 0 := congrArg (fun c : LongFieldCode => c.1) h
    exact absurd e (by decide)
  | .entry a l m, .entry b l' m', h => by
    have e₁ : a = b := congrArg (fun c : LongFieldCode => c.2.1) h
    have e₂ : l = l' := noteInj l l' (congrArg (fun c : LongFieldCode => c.2.2.1) h)
    have e₃ : m = m' := noteInj m m' (congrArg (fun c : LongFieldCode => c.2.2.2) h)
    rw [e₁,e₂,e₃]

private theorem operandInj : ∀ (op op' : LowerOperand), op.code = op'.code → op = op'
  | .coordinate r, .coordinate r', h => by
    have e : r = r' := congrArg (fun c : LowerOperandCode => c.2.1) h
    rw [e]
  | .ordinary r F, .ordinary r' G, h => by
    have e₁ : r = r' := congrArg (fun c : LowerOperandCode => c.2.1) h
    have e₂ : F = G := fieldInj F G (congrArg (fun c : LowerOperandCode => c.2.2) h)
    rw [e₁,e₂]
  | .count r l m, .count r' l' m', h => by
    have e₁ : r = r' := congrArg (fun c : LowerOperandCode => c.2.1) h
    have e₂ : ValueField.entry 0 l m = ValueField.entry 0 l' m' :=
      fieldInj (.entry 0 l m) (.entry 0 l' m') (congrArg (fun c : LowerOperandCode => c.2.2) h)
    injection e₂ with _ e₃ e₄
    rw [e₁,e₃,e₄]
  | .coordinate _, .ordinary _ _, h => by
    have e : (0 : Nat) = 1 := congrArg (fun c : LowerOperandCode => c.1) h
    exact absurd e (by decide)
  | .coordinate _, .count _ _ _, h => by
    have e : (0 : Nat) = 2 := congrArg (fun c : LowerOperandCode => c.1) h
    exact absurd e (by decide)
  | .ordinary _ _, .coordinate _, h => by
    have e : (1 : Nat) = 0 := congrArg (fun c : LowerOperandCode => c.1) h
    exact absurd e (by decide)
  | .ordinary _ _, .count _ _ _, h => by
    have e : (1 : Nat) = 2 := congrArg (fun c : LowerOperandCode => c.1) h
    exact absurd e (by decide)
  | .count _ _ _, .coordinate _, h => by
    have e : (2 : Nat) = 0 := congrArg (fun c : LowerOperandCode => c.1) h
    exact absurd e (by decide)
  | .count _ _ _, .ordinary _ _, h => by
    have e : (2 : Nat) = 1 := congrArg (fun c : LowerOperandCode => c.1) h
    exact absurd e (by decide)

theorem exactOperandCodeInjective : ExactOperandCodeInjective := operandInj

/-! ## Effectivity -/

private theorem remPrimitive : Primrec encodedOrdinalFiniteRemainder :=
  (OrdinalComparison.OrdinalSuccessorProgram.primitive).1

private theorem limitPrimitive : Primrec limitCode :=
  Primrec.and.comp ((Primrec.nat_lt.comp (Primrec.const 0) Primrec.id).decide)
    ((Primrec.eq.comp remPrimitive (Primrec.const 0)).decide)

private theorem fieldPrimitive : Primrec properFieldCode := by
  have tag : Primrec (fun c : LongFieldCode => c.1) := Primrec.fst
  have up : Primrec (fun c : LongFieldCode => c.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have low : Primrec (fun c : LongFieldCode => c.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have compare : Primrec₂ rawComparisonCode := rawComparisonPrimitiveRecursive
  have cmp : Primrec (fun c : LongFieldCode => rawComparisonCode c.2.2.2 c.2.2.1) :=
    compare.comp low up
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) (Primrec.const true)
    (Primrec.and.comp
      (Primrec.and.comp (limitPrimitive.comp up)
        (Primrec.or.comp ((Primrec.eq.comp low (Primrec.const 0)).decide) (limitPrimitive.comp low)))
      ((Primrec.eq.comp cmp (Primrec.const 0)).decide))

private theorem operandPrimitive : Primrec properOperandCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have field : Primrec (fun op : LowerOperandCode => op.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) (Primrec.const true)
    (fieldPrimitive.comp field)

private theorem listAll {A : Type} [Primcodable A] {p : A → Bool} (hp : Primrec p) :
    Primrec (fun xs : List A => xs.all p) := by
  have step : Primrec (fun q : A × Bool => p q.1 && q.2) :=
    Primrec.and.comp (hp.comp Primrec.fst) Primrec.snd
  apply (Primrec.list_foldr Primrec.id (Primrec.const true) (step.comp Primrec.snd).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (p x && xs.foldr (fun item acc => p item && acc) true) = (p x && xs.all p)
    exact congrArg (fun b => p x && b) ih

private theorem filterPrimitive {A : Type} [Primcodable A] {q : A → Bool} (hq : Primrec q) :
    Primrec (fun L : List A => L.filter q) := by
  have hp : PrimrecPred (fun a => q a = true) :=
    Primrec.primrecPred (hq.of_eq (fun a => by simp))
  exact (Primrec.listFilter hp).of_eq (fun L => by simp)

private theorem rowPrimitive : Primrec admittedRowCode := by
  have test : Primrec (fun r : RawBitRow => r.1.1) := Primrec.fst.comp Primrec.fst
  have operands : Primrec (fun r : RawBitRow => r.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have each : Primrec (fun t : WeightedCode => properOperandCode t.2) :=
    operandPrimitive.comp Primrec.snd
  have admitted : Primrec admittedCode := ActualBitFamilyRawClosed.exactClosedRawEffectivity.1
  exact Primrec.and.comp (admitted.comp test) ((listAll each).comp operands)

private theorem clausePrimitive : Primrec admittedClauseCode := listAll rowPrimitive

private theorem familyPrimitive : Primrec properClausesCode := filterPrimitive clausePrimitive

theorem exactRawProperClauseEffectivity : ExactRawProperClauseEffectivity :=
  ⟨limitPrimitive,fieldPrimitive,operandPrimitive,rowPrimitive,clausePrimitive,familyPrimitive,
    familyPrimitive.to_comp⟩

theorem fullRawProperClause : FullRawProperClause :=
  ⟨exactLimitCode,exactProperFieldCode,exactProperOperandCode,exactAdmittedTestCode,
    exactAdmittedRowCode,exactAdmittedClauseCode,exactRawProperClauses,exactOperandCodeInjective,
    exactRawProperClauseEffectivity⟩

#print axioms exactRawProperClauses
#print axioms fullRawProperClause

end LogicLineages.PermittedControl.RawProperClause

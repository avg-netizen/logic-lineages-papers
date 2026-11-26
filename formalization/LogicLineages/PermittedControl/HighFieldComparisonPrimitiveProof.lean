module
public import LogicLineages.PermittedControl.HighFieldComparisonTargets
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.PermittedControl.LongFieldTailPrimitiveProof
import LogicLineages.PermittedControl.RawFieldComparisonFormPrimitiveProof
import LogicLineages.PermittedControl.ThresholdNumericProgramsProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem normalize_code_if (P : LongFieldCode) :
    normalizeHighFieldCode P =
      if P.1 = 0 then P else
        let k := shortIterateCode P.2.2.1 P.2.2.2 P.2.1
        if k = 0 then P else (0,k - 1,0,0) := by
  rcases P with ⟨tag,a,lam,mu⟩
  by_cases h : tag = 0
  · simp [normalizeHighFieldCode,h]
  · cases hk : shortIterateCode lam mu a <;>
      simp [normalizeHighFieldCode,h,hk]

private theorem normalizeHighFieldCode_primrec : Primrec normalizeHighFieldCode := by
  have ht : Primrec (fun p : LongFieldCode => p.1) := Primrec.fst
  have ha : Primrec (fun p : LongFieldCode => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : LongFieldCode => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun p : LongFieldCode => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hk := shortFieldPreprocessingEffective.2.2.1.comp (hl.pair (hm.pair ha))
  have hz : Primrec (fun _ : LongFieldCode => (0 : Nat)) := Primrec.const 0
  have hnew := hz.pair ((Primrec.nat_sub.comp hk (Primrec.const 1)).pair (hz.pair hz))
  exact (Primrec.ite (Primrec.eq.comp ht hz) Primrec.id
    (Primrec.ite (Primrec.eq.comp hk hz) Primrec.id hnew)).of_eq
    (fun p => (normalize_code_if p).symm)

private theorem highShortBoundCode_primrec : Primrec₂ highShortBoundCode := by
  have hB : Primrec (fun p : Nat × LongFieldCode => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat × LongFieldCode => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : Nat × LongFieldCode => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec (fun p : Nat × LongFieldCode => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (Primrec.const 0)
    (shortFieldPreprocessingEffective.2.2.2.1.comp (hl.pair (hm.pair hB)))

/-- Pure max composition over five opaque function arguments. This
elaborates independently of the notation and certificate routines. -/
private theorem stagedMaxBound_primrec {α : Type*} [Primcodable α]
    {a b c d e : α → Nat} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (he : Primrec e) :
    Primrec (fun p => max (max (a p) (b p)) (max (c p) (max (d p) (e p)))) := by
  have hab := Primrec.nat_max.comp ha hb
  have hde := Primrec.nat_max.comp hd he
  have hcde := Primrec.nat_max.comp hc hde
  exact Primrec.nat_max.comp hab hcde

private abbrev BoundArgs := Nat × LongFieldCode × LongFieldCode

private def budgetArg (p : BoundArgs) : Nat := p.1
private def leftFieldArg (p : BoundArgs) : LongFieldCode := p.2.1
private def rightFieldArg (p : BoundArgs) : LongFieldCode := p.2.2
private def normalizedLeftFieldArg (p : BoundArgs) : LongFieldCode :=
  normalizeHighFieldCode (leftFieldArg p)
private def normalizedRightFieldArg (p : BoundArgs) : LongFieldCode :=
  normalizeHighFieldCode (rightFieldArg p)

private def forwardBoundArgs (p : BoundArgs) : BoundArgs :=
  (budgetArg p, normalizedLeftFieldArg p, normalizedRightFieldArg p)
private def reverseBoundArgs (p : BoundArgs) : BoundArgs :=
  (budgetArg p, normalizedRightFieldArg p, normalizedLeftFieldArg p)

private theorem budgetArg_primrec : Primrec budgetArg := Primrec.fst
private theorem leftFieldArg_primrec : Primrec leftFieldArg := Primrec.fst.comp Primrec.snd
private theorem rightFieldArg_primrec : Primrec rightFieldArg := Primrec.snd.comp Primrec.snd
private theorem normalizedLeftFieldArg_primrec : Primrec normalizedLeftFieldArg :=
  normalizeHighFieldCode_primrec.comp leftFieldArg_primrec
private theorem normalizedRightFieldArg_primrec : Primrec normalizedRightFieldArg :=
  normalizeHighFieldCode_primrec.comp rightFieldArg_primrec
private theorem forwardBoundArgs_primrec : Primrec forwardBoundArgs :=
  budgetArg_primrec.pair (normalizedLeftFieldArg_primrec.pair normalizedRightFieldArg_primrec)
private theorem reverseBoundArgs_primrec : Primrec reverseBoundArgs :=
  budgetArg_primrec.pair (normalizedRightFieldArg_primrec.pair normalizedLeftFieldArg_primrec)

private theorem shortLeftBound_primrec :
    Primrec (fun p : BoundArgs => highShortBoundCode (budgetArg p) (leftFieldArg p)) :=
  highShortBoundCode_primrec.comp budgetArg_primrec leftFieldArg_primrec

private theorem shortRightBound_primrec :
    Primrec (fun p : BoundArgs => highShortBoundCode (budgetArg p) (rightFieldArg p)) :=
  highShortBoundCode_primrec.comp budgetArg_primrec rightFieldArg_primrec

private theorem sameHighBound_primrec :
    Primrec (fun p : BoundArgs => longFieldSameBoundCode
      (forwardBoundArgs p).1 (forwardBoundArgs p).2.1 (forwardBoundArgs p).2.2) :=
  longFieldSameBoundCode_primrec.comp forwardBoundArgs_primrec

private theorem forwardHighBound_primrec :
    Primrec (fun p : BoundArgs => longFieldDistinctBoundCode
      (forwardBoundArgs p).1 (forwardBoundArgs p).2.1 (forwardBoundArgs p).2.2) :=
  longFieldDistinctBoundCode_primrec.comp forwardBoundArgs_primrec

private theorem reverseHighBound_primrec :
    Primrec (fun p : BoundArgs => longFieldDistinctBoundCode
      (reverseBoundArgs p).1 (reverseBoundArgs p).2.1 (reverseBoundArgs p).2.2) :=
  longFieldDistinctBoundCode_primrec.comp reverseBoundArgs_primrec

private theorem highFieldComparisonBoundCode_primrec :
    Primrec (fun p : Nat × LongFieldCode × LongFieldCode =>
      highFieldComparisonBoundCode p.1 p.2.1 p.2.2) := by
  exact (stagedMaxBound_primrec shortLeftBound_primrec shortRightBound_primrec sameHighBound_primrec
    forwardHighBound_primrec reverseHighBound_primrec).of_eq (fun _ => rfl)

private theorem flipHighComparisonAnswer_primrec : Primrec₂ flipHighComparisonAnswer := by
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.snd
    (reverseComparisonCode_primrec.comp Primrec.snd)

private theorem rawConstForm_primrec : Primrec rawConstForm :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const (0,0,0,0)))

private theorem highRawComparisonForm_primrec :
    Primrec (fun p : LongFieldCode × LongFieldCode × Nat × Nat =>
      highRawComparisonForm p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hP : Primrec (fun p : LongFieldCode × LongFieldCode × Nat × Nat => p.1) := Primrec.fst
  have hQ : Primrec (fun p : LongFieldCode × LongFieldCode × Nat × Nat => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : LongFieldCode × LongFieldCode × Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy : Primrec (fun p : LongFieldCode × LongFieldCode × Nat × Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hNP := normalizeHighFieldCode_primrec.comp hP
  have hNQ := normalizeHighFieldCode_primrec.comp hQ
  exact Primrec.ite (Primrec.nat_lt.comp hx hy)
    ((Primrec.const 0).pair (rawFieldComparisonFormEffective.1.comp hNP hNQ))
    (Primrec.ite (Primrec.nat_lt.comp hy hx)
      ((Primrec.const 1).pair (rawFieldComparisonFormEffective.1.comp hNQ hNP))
      ((Primrec.const 0).pair (rawConstForm_primrec.comp (rawFieldComparisonFormEffective.2.comp hNP hNQ))))

theorem highFieldComparisonEffective : HighFieldComparisonEffective :=
  ⟨normalizeHighFieldCode_primrec,highShortBoundCode_primrec,highFieldComparisonBoundCode_primrec,
    flipHighComparisonAnswer_primrec,highRawComparisonForm_primrec⟩

end LogicLineages.PermittedControl.FieldComparison

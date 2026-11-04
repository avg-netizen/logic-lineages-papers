module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetProof
open Source NumberedAuxiliaryCoding NumberedFiniteMarkPrimrec NumberedMultisetCertificate
open NumberedMultisetNumeric NumberedUniformPackedDecoding NumberedUniformMultiset
open NumberedMulPrimrecSupportProof (optionAnyPrimitive)

attribute [local irreducible] Primrec rawPackedDecode decodeNumbers

theorem certificateDecoderCalibration :
    NumberedUniformMultisetTargets.ActualCertificateDecoderCalibration :=
  NumberedUniformMultisetSupportProof.certificateDecoderCalibration

theorem multisetCalibration : NumberedUniformMultisetTargets.ActualMultisetCalibration :=
  NumberedUniformMultisetSupportProof.multisetCalibration

theorem rawMarkPrimitive (n : Nat) :
    Primrec (fun p : Nat × RawPacked n => rawMark p.1 p.2) := by
  have hcode : Primrec (fun p : Nat × RawPacked n => finiteMarkCode p.1 p.2.2) :=
    (NumberedFiniteMarkPrimrecProof.finiteMarkCodePrimitive n).comp
      (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_map hcode
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).to₂

private def witnessTest {n : Nat} (removed : List (RawPacked n))
    (q : RawPacked n) (witness : MarkWitness) : Bool :=
  (removed[witness.1]?).any (fun s => decide (rawMark witness.2 s = some q))

private theorem witnessTestPrimitive (n : Nat) :
    Primrec (fun p : List (RawPacked n) × RawPacked n × MarkWitness =>
      witnessTest p.1 p.2.1 p.2.2) := by
  apply optionAnyPrimitive
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  exact ((Primrec.eq.comp
    ((rawMarkPrimitive n).comp
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
    (Primrec.option_some.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).decide).to₂

private def replacementStep {n : Nat} (removed : List (RawPacked n))
    (state : List (RawPacked n) × Bool) (witness : MarkWitness) : List (RawPacked n) × Bool :=
  (state.1.tail, state.2 && state.1.head?.any (fun q => witnessTest removed q witness))

private def replacementFinish {n : Nat} (state : List (RawPacked n) × Bool) : Bool :=
  decide (state.1 = []) && state.2

private theorem replacementFoldCalibration (n : Nat) (removed inserted : List (RawPacked n))
    (witnesses : List MarkWitness) (valid : Bool) :
    replacementFinish (witnesses.foldl (replacementStep removed) (inserted, valid)) =
      (valid && rawReplacementTest removed inserted witnesses) := by
  induction witnesses generalizing inserted valid with
  | nil => cases inserted <;> cases valid <;> rfl
  | cons witness witnesses ih =>
    rcases witness with ⟨index, label⟩
    cases inserted with
    | nil =>
      simpa [List.foldl_cons, replacementStep, replacementFinish, rawReplacementTest] using
        (ih [] false)
    | cons q rest =>
      simp only [List.foldl_cons, replacementStep, List.tail_cons, List.head?_cons, Option.any_some]
      rw [ih]
      cases h : removed[index]? with
      | none => simp [witnessTest, h, rawReplacementTest]
      | some s => simp [witnessTest, h, rawReplacementTest, Bool.and_assoc]

private theorem replacementStepPrimitive (n : Nat) :
    Primrec (fun p : List (RawPacked n) × (List (RawPacked n) × Bool) × MarkWitness =>
      replacementStep p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : List (RawPacked n) × (List (RawPacked n) × Bool) × MarkWitness =>
      p.2.1.1.tail) :=
    Primrec.list_tail.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hh : Primrec (fun p : List (RawPacked n) × (List (RawPacked n) × Bool) × MarkWitness =>
      p.2.1.1.head?.any (fun q => witnessTest p.1 q p.2.2)) :=
    optionAnyPrimitive
      (Primrec.list_head?.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      ((witnessTestPrimitive n).comp
        ((Primrec.fst.comp Primrec.fst).pair
          (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂
  exact ht.pair (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hh)

theorem rawReplacementPrimitive (n : Nat) :
    Primrec (fun p : List (RawPacked n) × List (RawPacked n) × List MarkWitness =>
      rawReplacementTest p.1 p.2.1 p.2.2) := by
  have hfold : Primrec (fun p : List (RawPacked n) × List (RawPacked n) × List MarkWitness =>
      p.2.2.foldl (replacementStep p.1) (p.2.1, true)) :=
    Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.const true))
      ((replacementStepPrimitive n).comp
        ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have hfinish : Primrec (@replacementFinish n) :=
    Primrec.and.comp (Primrec.eq.comp Primrec.fst (Primrec.const [])).decide Primrec.snd
  exact (hfinish.comp hfold).of_eq (by
    intro p
    simpa using replacementFoldCalibration n p.1 p.2.1 p.2.2 true)

theorem rawMultisetPrimitive : NumberedUniformMultisetTargets.ActualRawMultisetPrimitive := by
  intro n
  have hc : Primrec (fun p : List (RawPacked n) × List (RawPacked n) × RawCertificate n =>
      p.2.2) := Primrec.snd.comp Primrec.snd
  have hk := Primrec.fst.comp hc
  have hr := Primrec.fst.comp (Primrec.snd.comp hc)
  have hi := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hw := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hp := NumberedExchangeGuardsPrimrecProof.permutationPrimitive (RawPacked n)
  have hleft := hp.comp (Primrec.fst.pair (Primrec.list_append.comp hk hr))
  have hright := hp.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.list_append.comp hk hi))
  have hnonempty := (Primrec.eq.comp hr (Primrec.const [])).not.decide
  have hwitnesses := (rawReplacementPrimitive n).comp (hr.pair (hi.pair hw))
  exact (Primrec.and.comp (Primrec.and.comp hleft (Primrec.and.comp hright hnonempty)) hwitnesses).of_eq
    (by intro p; simp only [rawMultisetTest, Bool.decide_and])

theorem packedNumbersDecoderPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : List Ty × List Nat => decodeRawPackedNumbers n arity p.1 p.2) := by
  let Input := List Ty × List Nat
  let L := List (RawPacked n)
  let Step := Input × (Nat × Option L)
  have hstep : Primrec₂ (fun (input : Input) (p : Nat × Option L) =>
      (rawPackedDecode n arity input.1 p.1).bind (fun q => p.2.map (q :: ·))) := by
    change Primrec (fun p : Step =>
      (rawPackedDecode n arity p.1.1 p.2.1).bind (fun q => p.2.2.map (q :: ·)))
    apply Primrec.option_bind
      (f := fun p : Step => rawPackedDecode n arity p.1.1 p.2.1)
      (g := fun (p : Step) (q : RawPacked n) => p.2.2.map (q :: ·))
      ((NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
    apply Primrec.option_map
      (f := fun p : Step × RawPacked n => p.1.2.2)
      (g := fun (p : Step × RawPacked n) (qs : L) => p.2 :: qs)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hfold := Primrec.list_foldr Primrec.snd (Primrec.const (some ([] : L))) hstep
  apply hfold.of_eq
  rintro ⟨Gamma, values⟩
  induction values <;> simp_all [decodeRawPackedNumbers, Option.map_eq_bind]

theorem packedListDecoderPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : List Ty × Nat => decodeRawPackedList n arity p.1 p.2) := by
  exact Primrec.option_bind
    (f := fun p : List Ty × Nat => decodeNumbers p.2)
    (g := fun (p : List Ty × Nat) (values : List Nat) => decodeRawPackedNumbers n arity p.1 values)
    (NumberedListCodecPrimrecProof.decoderPrimitive.comp Primrec.snd)
    ((packedNumbersDecoderPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

attribute [local irreducible] decodeRawPackedNumbers decodeRawPackedList

theorem certificateDecoderPrimitive :
    NumberedUniformMultisetTargets.ActualUniformCertificateDecoderPrimitive := by
  intro n arity
  let Input := List Ty × Nat
  let L := List (RawPacked n)
  have hl := packedListDecoderPrimitive n arity
  have hu : Primrec (fun value : Nat => (Nat.unpair value).2) := Primrec.snd.comp Primrec.unpair
  have hi : Primrec (fun value : Nat => (Nat.unpair value).1) := Primrec.fst.comp Primrec.unpair
  have hw : Primrec (fun values : List Nat => values.map Nat.unpair) :=
    Primrec.list_map Primrec.id (Primrec.unpair.comp Primrec.snd).to₂
  unfold decodeRawCertificate
  apply Primrec.option_bind
    (g := fun (p : Input) (kept : L) => do
      let removed ← decodeRawPackedList n arity p.1 (Nat.unpair (Nat.unpair p.2).2).1
      let inserted ← decodeRawPackedList n arity p.1 (Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).1
      let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2
      pure ((kept, removed, inserted, witnesses.map Nat.unpair) : RawCertificate n))
    (hl.comp (Primrec.fst.pair (hi.comp Primrec.snd)))
  change Primrec (fun p : Input × L => do
    let removed ← decodeRawPackedList n arity p.1.1 (Nat.unpair (Nat.unpair p.1.2).2).1
    let inserted ← decodeRawPackedList n arity p.1.1 (Nat.unpair (Nat.unpair (Nat.unpair p.1.2).2).2).1
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.2).2).2).2
    pure ((p.2, removed, inserted, witnesses.map Nat.unpair) : RawCertificate n))
  apply Primrec.option_bind
    (g := fun (p : Input × L) (removed : L) => do
      let inserted ← decodeRawPackedList n arity p.1.1 (Nat.unpair (Nat.unpair (Nat.unpair p.1.2).2).2).1
      let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.2).2).2).2
      pure ((p.2, removed, inserted, witnesses.map Nat.unpair) : RawCertificate n))
    (hl.comp ((Primrec.fst.comp Primrec.fst).pair
      (hi.comp (hu.comp (Primrec.snd.comp Primrec.fst)))))
  change Primrec (fun p : (Input × L) × L => do
    let inserted ← decodeRawPackedList n arity p.1.1.1 (Nat.unpair (Nat.unpair (Nat.unpair p.1.1.2).2).2).1
    let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.1.2).2).2).2
    pure ((p.1.2, p.2, inserted, witnesses.map Nat.unpair) : RawCertificate n))
  apply Primrec.option_bind
    (g := fun (p : (Input × L) × L) (inserted : L) => do
      let witnesses ← decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.1.2).2).2).2
      pure ((p.1.2, p.2, inserted, witnesses.map Nat.unpair) : RawCertificate n))
    (hl.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (hi.comp (hu.comp (hu.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))))
  change Primrec (fun p : ((Input × L) × L) × L =>
    (decodeNumbers (Nat.unpair (Nat.unpair (Nat.unpair p.1.1.1.2).2).2).2).bind
      (fun witnesses => some ((p.1.1.2, p.1.2, p.2, witnesses.map Nat.unpair) : RawCertificate n)))
  apply Primrec.option_bind
    (g := fun (p : ((Input × L) × L) × L) (witnesses : List Nat) =>
      some ((p.1.1.2, p.1.2, p.2, witnesses.map Nat.unpair) : RawCertificate n))
    (NumberedListCodecPrimrecProof.decoderPrimitive.comp
      (hu.comp (hu.comp (hu.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))))
  exact (Primrec.option_some.comp
    ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair (hw.comp Primrec.snd))))).to₂

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMultisetProof

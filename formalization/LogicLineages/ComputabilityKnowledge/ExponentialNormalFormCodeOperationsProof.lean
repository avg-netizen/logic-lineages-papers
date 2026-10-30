module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodeOperations
public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsEffectivity

@[expose] public section

/-! Codex constructive implementation proof. These operations denote the
actual existing finite maps; numerical-function equality is not used as a
substitute for structural key equality. The complete gate remains pending
until every frozen operation and its genuine effectivity supplier is closed.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsProof

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormCodeOperations ExponentialNormalizer
open ExponentialNormalFormProduct
open ExponentialHereditaryCodecProof ExponentialNormalFormCodecProof

noncomputable section

local instance {d h : Nat} : DecidableEq (Form d h) := Classical.decEq _

theorem canonicalEntries_keys (d h n : Nat) :
    MapCanonical d (canonicalEntries d (h + 1) n) ∧
    ∀ e ∈ canonicalEntries d (h + 1) n, CodeCanonical d h e.1 := by
  obtain ⟨es, he, hcanon, hkeys⟩ := (canonicalization d (h + 1) n).1
  simpa [canonicalEntries, he] using And.intro hcanon hkeys

theorem canonicalEntries_decode (d h n : Nat) :
    entriesDecode d h (canonicalEntries d (h + 1) n) = formDecode d (h + 1) n :=
  (canonicalization d (h + 1) n).2

theorem entriesDecode_append (d h : Nat) (xs ys : MapCode) :
    entriesDecode d h (xs ++ ys) = entriesDecode d h xs + entriesDecode d h ys := by
  induction xs with
  | nil => simp [entriesDecode]
  | cons e xs ih =>
      simpa [entriesDecode, add_assoc] using congrArg
        (fun z => Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + z) ih

theorem variableCodes : Comparators.ExponentialNormalFormCodeOperations.Variables := by
  intro d h i
  cases h with
  | zero =>
      refine ⟨⟨coeffVariable d i.val, rfl, canon_variable d i.val⟩, ?_⟩
      change formDecode d 0 (Encodable.encode (coeffVariable d i.val)) =
        ExponentialNormalizer.affineVariable i
      rw [formDecode_zero_encode]
      unfold ExponentialNormalizer.affineVariable
      exact decode_variable d i
  | succ h =>
      refine ⟨canonical_encode_normalizeMap d h _ ?_, ?_⟩
      · intro e he
        simp only [List.mem_singleton] at he
        subst e
        exact zeroCode_canonical d h
      · change formDecode d (h + 1) (Encodable.encode
          (normalizeMap d [(zeroCode d h, coeffVariable d i.val)])) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap]
        have hv : coeffDecode d (coeffVariable d i.val) =
            ExponentialNormalizer.affineVariable i := by
          unfold ExponentialNormalizer.affineVariable
          exact decode_variable d i
        simp [entriesDecode, hv, variableForm]

theorem additionCodes : Comparators.ExponentialNormalFormCodeOperations.Addition := by
  intro d h a b
  cases h with
  | zero =>
      refine ⟨⟨coeffAdd d (parseCoefficients a) (parseCoefficients b), rfl,
        canon_add d _ _⟩, ?_⟩
      simpa [addCode, addForm, formDecode] using
        decode_add d (parseCoefficients a) (parseCoefficients b)
  | succ h =>
      refine ⟨canonical_encode_normalizeMap d h _ ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with ha | hb
        · exact (canonicalEntries_keys d h a).2 e ha
        · exact (canonicalEntries_keys d h b).2 e hb
      · change formDecode d (h + 1) (Encodable.encode (normalizeMap d
          (canonicalEntries d (h + 1) a ++ canonicalEntries d (h + 1) b))) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap, entriesDecode_append,
          canonicalEntries_decode, canonicalEntries_decode]
        rfl

theorem decodedKey_zero_iff (d h k : Nat) (hk : CodeCanonical d h k) :
    formDecode d h k = zeroForm h ↔ k = zeroCode d h := by
  simpa only [zeroCode_decode] using
    faithfulness d h k (zeroCode d h) hk (zeroCode_canonical d h)

theorem entries_constantCoefficient (d h : Nat) : ∀ es : MapCode,
    (∀ e ∈ es, CodeCanonical d h e.1) →
    constantCoefficient (h + 1) (entriesDecode d h es) =
      es.foldr (fun e acc => if e.1 = zeroCode d h then e.2.getD 0 0 + acc else acc) 0
  | [], _ => rfl
  | e :: es, hkeys => by
      have htail : ∀ a ∈ es, CodeCanonical d h a.1 :=
        fun a ha => hkeys a (List.mem_cons_of_mem e ha)
      have ih := entries_constantCoefficient d h es htail
      change (entriesDecode d h es) (zeroForm h) 0 = _ at ih
      have hkey := hkeys e List.mem_cons_self
      change ((Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) +
        entriesDecode d h es) (zeroForm h)) 0 = _
      rw [Finsupp.add_apply, Pi.add_apply]
      by_cases he : e.1 = zeroCode d h
      · have hz := (decodedKey_zero_iff d h e.1 hkey).mpr he
        simp [Finsupp.single_apply, hz, he, ih, coeffDecode]
      · have hz : formDecode d h e.1 ≠ zeroForm h := by
          intro hzero
          exact he ((decodedKey_zero_iff d h e.1 hkey).mp hzero)
        simp [Finsupp.single_apply, hz, Ne.symm hz, he, ih]

theorem constantCoefficientCode_correct (d h n : Nat) :
    constantCoefficientCode d h n = constantCoefficient h (formDecode d h n) := by
  cases h with
  | zero => rfl
  | succ h =>
      change (canonicalEntries d (h + 1) n).foldr
        (fun e acc => if e.1 = zeroCode d h then e.2.getD 0 0 + acc else acc) 0 = _
      rw [← canonicalEntries_decode d h n]
      exact (entries_constantCoefficient d h _ (canonicalEntries_keys d h n).2).symm

theorem affineRemove_apply {d : Nat} (a : Affine d) (i : Fin (d + 1)) :
    affineRemoveConstant a i = if i = 0 then 0 else a i := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [affineRemoveConstant]

theorem remove_succ_apply {d : Nat} (h : Nat) (f : Form d (h + 1))
    (key : Form d h) (i : Fin (d + 1)) :
    removeConstant (h + 1) f key i =
      if key = zeroForm h ∧ i = 0 then 0 else f key i := by
  classical
  change (f.update (zeroForm h) (affineRemoveConstant (f (zeroForm h)))) key i = _
  rw [Finsupp.update_apply]
  by_cases hk : key = zeroForm h
  · subst key
    simp [affineRemove_apply]
  · simp [hk]

theorem remove_succ_zero {d : Nat} (h : Nat) :
    removeConstant (h + 1) (0 : Form d (h + 1)) = 0 := by
  apply Finsupp.ext
  intro key
  funext i
  rw [remove_succ_apply (d := d) h 0 key i]
  simp

theorem remove_succ_add {d : Nat} (h : Nat) (f g : Form d (h + 1)) :
    removeConstant (h + 1) (f + g) =
      removeConstant (h + 1) f + removeConstant (h + 1) g := by
  classical
  apply Finsupp.ext
  intro key
  funext i
  rw [remove_succ_apply (d := d) h (f + g) key i]
  simp only [Finsupp.add_apply, Pi.add_apply]
  rw [remove_succ_apply (d := d) h f key i, remove_succ_apply (d := d) h g key i]
  split_ifs <;> simp

theorem remove_succ_single (d h k : Nat) (c : CoeffCode)
    (hk : CodeCanonical d h k) :
    removeConstant (h + 1) (Finsupp.single (formDecode d h k) (coeffDecode d c)) =
      Finsupp.single (formDecode d h k)
        (coeffDecode d (if k = zeroCode d h then coeffRemove d c else c)) := by
  classical
  by_cases he : k = zeroCode d h
  · have hz := (decodedKey_zero_iff d h k hk).mpr he
    simp only [if_pos he, decode_remove]
    apply Finsupp.ext
    intro key
    funext i
    rw [remove_succ_apply (d := d) h _ key i]
    by_cases hkey : key = zeroForm h
    · subst key
      simp [remove_succ_apply, Finsupp.single_apply, hz, affineRemove_apply]
    · simp [remove_succ_apply, Finsupp.single_apply, hz, hkey, Ne.symm hkey]
  · have hz : formDecode d h k ≠ zeroForm h := by
      intro hzero
      exact he ((decodedKey_zero_iff d h k hk).mp hzero)
    simp only [if_neg he]
    apply Finsupp.ext
    intro key
    funext i
    rw [remove_succ_apply (d := d) h _ key i]
    by_cases hkey : key = zeroForm h
    · subst key
      simp [remove_succ_apply, Finsupp.single_apply, hz, Ne.symm hz]
    · simp [remove_succ_apply, hkey]

theorem entriesDecode_remove (d h : Nat) : ∀ es : MapCode,
    (∀ e ∈ es, CodeCanonical d h e.1) →
    entriesDecode d h (es.map (fun e =>
      (e.1, if e.1 = zeroCode d h then coeffRemove d e.2 else e.2))) =
      removeConstant (h + 1) (entriesDecode d h es)
  | [], _ => (remove_succ_zero h).symm
  | e :: es, hkeys => by
      have htail : ∀ a ∈ es, CodeCanonical d h a.1 :=
        fun a ha => hkeys a (List.mem_cons_of_mem e ha)
      change Finsupp.single (formDecode d h e.1)
        (coeffDecode d (if e.1 = zeroCode d h then coeffRemove d e.2 else e.2)) +
        entriesDecode d h (es.map (fun e =>
          (e.1, if e.1 = zeroCode d h then coeffRemove d e.2 else e.2))) =
        removeConstant (h + 1)
          (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + entriesDecode d h es)
      rw [remove_succ_add]
      congr 1
      · exact (remove_succ_single d h e.1 e.2 (hkeys e List.mem_cons_self)).symm
      · exact entriesDecode_remove d h es htail

theorem constantRemovalCodes : Comparators.ExponentialNormalFormCodeOperations.ConstantRemoval := by
  intro d h n
  refine ⟨constantCoefficientCode_correct d h n, ?_, ?_⟩
  · cases h with
    | zero => exact ⟨coeffRemove d (parseCoefficients n), rfl, canon_remove d _⟩
    | succ h =>
        apply canonical_encode_normalizeMap
        intro e he
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
        exact (canonicalEntries_keys d h n).2 a ha
  · cases h with
    | zero => simpa [removeCode, removeConstant, formDecode] using
        decode_remove d (parseCoefficients n)
    | succ h =>
        change formDecode d (h + 1) (Encodable.encode (normalizeMap d
          ((canonicalEntries d (h + 1) n).map (fun e =>
            (e.1, if e.1 = zeroCode d h then coeffRemove d e.2 else e.2))))) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap,
          entriesDecode_remove d h _ (canonicalEntries_keys d h n).2,
          canonicalEntries_decode]

theorem entriesDecode_raise_keys (d h : Nat) (es : MapCode)
    (hraise : ∀ n, formDecode d (h + 1) (raiseCode d h n) = raiseForm h (formDecode d h n)) :
    entriesDecode d (h + 1) (es.map (fun e => (raiseCode d h e.1, e.2))) =
      Finsupp.mapDomain (raiseForm h) (entriesDecode d h es) := by
  induction es with
  | nil => simp [entriesDecode, Finsupp.mapDomain_zero]
  | cons e es ih =>
      simpa [entriesDecode, hraise, Finsupp.mapDomain_add, Finsupp.mapDomain_single] using
        (congrArg (fun z => Finsupp.single (raiseForm h (formDecode d h e.1))
          (coeffDecode d e.2) + z) ih)

theorem heightTransportCodes : Comparators.ExponentialNormalFormCodeOperations.HeightTransport := by
  intro d h
  induction h with
  | zero =>
      intro n
      refine ⟨canonical_encode_normalizeMap d 0 _ ?_, ?_⟩
      · intro e he
        simp only [List.mem_singleton] at he
        subst e
        exact zeroCode_canonical d 0
      · change formDecode d 1 (Encodable.encode (normalizeMap d
          [(zeroCode d 0, coeffNormalize d (parseCoefficients n))])) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap]
        change Finsupp.single (formDecode d 0 (zeroCode d 0))
          (coeffDecode d (coeffNormalize d (parseCoefficients n))) + 0 =
            Finsupp.single (zeroForm 0) (formDecode d 0 n)
        rw [zeroCode_decode, decode_normalize, add_zero]
        rfl
  | succ h ih =>
      intro n
      refine ⟨canonical_encode_normalizeMap d (h + 1) _ ?_, ?_⟩
      · intro e he
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
        exact (ih a.1).1
      · change formDecode d ((h + 1) + 1) (Encodable.encode (normalizeMap d
          ((canonicalEntries d (h + 1) n).map (fun e => (raiseCode d h e.1, e.2))))) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap,
          entriesDecode_raise_keys d h _ (fun k => (ih k).2), canonicalEntries_decode]
        rfl

theorem codeOperations : Comparators.ExponentialNormalFormCodeOperations.Target :=
  ⟨variableCodes, additionCodes, constantRemovalCodes, heightTransportCodes,
    ExponentialNormalFormCodeOperationsEffectivity.actualPrimitiveRecursion⟩

end

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsProof

module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialHereditaryCodec
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section

/-! Codex constructive continuation after the read-only author reached its
usage limit without returning a proposal. The exact hereditary-code target
was independently compiled before this proof. Partial checked helpers do
not constitute acceptance of the whole target.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof

open ExponentialNormalForm ExponentialNormalFormCodec
open ExponentialHereditaryCodec ExponentialNormalFormCodecProof

@[simp] theorem parseCoefficients_encode (xs : CoeffCode) :
    parseCoefficients (Encodable.encode xs) = xs := by
  simp [parseCoefficients]

@[simp] theorem parseEntries_encode (es : MapCode) :
    parseEntries (Encodable.encode es) = es := by
  simp [parseEntries]

@[simp] theorem formDecode_zero_encode (d : Nat) (xs : CoeffCode) :
    formDecode d 0 (Encodable.encode xs) = coeffDecode d xs := by
  simp [formDecode]

noncomputable def entriesDecode (d h : Nat) (es : MapCode) : Form d (h + 1) :=
  es.foldr (fun e acc => Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + acc) 0

@[simp] theorem formDecode_succ_encode (d h : Nat) (es : MapCode) :
    formDecode d (h + 1) (Encodable.encode es) = entriesDecode d h es := by
  simp [formDecode, entriesDecode]

theorem entriesDecode_mapDomain (d h : Nat) (es : MapCode) :
    entriesDecode d h es = Finsupp.mapDomain (formDecode d h) (mapDecode d es) := by
  induction es with
  | nil => simp [entriesDecode, mapDecode, Finsupp.mapDomain_zero]
  | cons e es ih =>
      simpa [entriesDecode, mapDecode, Finsupp.mapDomain_add,
        Finsupp.mapDomain_single] using congrArg
          (fun z => Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + z) ih

theorem entriesDecode_normalizeMap (d h : Nat) (es : MapCode) :
    entriesDecode d h (normalizeMap d es) = entriesDecode d h es := by
  rw [entriesDecode_mapDomain, decode_normalizeMap, ← entriesDecode_mapDomain]

theorem entriesDecode_map_keys (d h : Nat) (F : Nat → Nat) (es : MapCode)
    (hF : ∀ k, formDecode d h (F k) = formDecode d h k) :
    entriesDecode d h (es.map (fun e => (F e.1, e.2))) = entriesDecode d h es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simpa [entriesDecode, hF] using (congrArg
        (fun z => Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + z) ih)

theorem normalizeMap_key_mem (d : Nat) (es : MapCode) (e : Nat × CoeffCode)
    (he : e ∈ normalizeMap d es) : ∃ a ∈ es, e.1 = a.1 := by
  induction es with
  | nil => simp [normalizeMap] at he
  | cons a es ih =>
      change e ∈ insertEntry d a.1 a.2 (normalizeMap d es) at he
      cases hz : coeffIsZero d a.2 with
      | true =>
          have he' : e ∈ normalizeMap d es := by simpa [insertEntry, hz] using he
          obtain ⟨b, hb, hkey⟩ := ih he'
          exact ⟨b, List.mem_cons_of_mem a hb, hkey⟩
      | false =>
          have he' : e ∈ insertRaw d a.1 (coeffNormalize d a.2) (normalizeMap d es) := by
            simpa [insertEntry, hz] using he
          rcases insertRaw_mem (normalizeMap d es) e he' with hkey | hm
          · exact ⟨a, List.mem_cons_self, hkey⟩
          · obtain ⟨b, hb, hkey⟩ := ih hm
            exact ⟨b, List.mem_cons_of_mem a hb, hkey⟩

theorem canonicalization : Comparators.ExponentialHereditaryCodec.Canonicalization := by
  intro d h
  induction h with
  | zero =>
      intro n
      refine ⟨⟨coeffNormalize d (parseCoefficients n), rfl,
        canon_normalize d _⟩, ?_⟩
      simpa [canonicalize, formDecode] using decode_normalize d (parseCoefficients n)
  | succ h ih =>
      intro n
      let es := (parseEntries n).map (fun e => (canonicalize d h e.1, e.2))
      refine ⟨⟨normalizeMap d es, rfl, normalize_canonical d es, ?_⟩, ?_⟩
      · intro e he
        obtain ⟨a, ha, hkey⟩ := normalizeMap_key_mem d es e he
        obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
        rw [← hb] at hkey
        rw [hkey]
        exact (ih b.1).1
      · change formDecode d (h + 1) (Encodable.encode (normalizeMap d es)) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap]
        exact entriesDecode_map_keys d h (canonicalize d h) (parseEntries n)
          (fun k => (ih k).2)

theorem mapDecode_support_key_mem (d : Nat) (es : MapCode) (k : Nat)
    (hk : k ∈ (mapDecode d es).support) : ∃ e ∈ es, k = e.1 := by
  classical
  induction es with
  | nil => simp [mapDecode] at hk
  | cons e es ih =>
      change k ∈ (Finsupp.single e.1 (coeffDecode d e.2) + mapDecode d es).support at hk
      rcases Finset.mem_union.mp (Finsupp.support_add hk) with hs | hr
      · exact ⟨e, List.mem_cons_self,
          Finset.mem_singleton.mp (Finsupp.support_single_subset hs)⟩
      · obtain ⟨a, ha, heq⟩ := ih hr
        exact ⟨a, List.mem_cons_of_mem e ha, heq⟩

theorem support_canonical_keys (d h : Nat) (es : MapCode)
    (hkeys : ∀ e ∈ es, CodeCanonical d h e.1) :
    ((mapDecode d es).support : Set Nat) ⊆ {k | CodeCanonical d h k} := by
  intro k hk
  obtain ⟨e, he, rfl⟩ := mapDecode_support_key_mem d es k hk
  exact hkeys e he

theorem faithfulness : Comparators.ExponentialHereditaryCodec.Faithfulness := by
  intro d h
  induction h with
  | zero =>
      intro n m hn hm
      obtain ⟨xs, rfl, hxs⟩ := hn
      obtain ⟨ys, rfl, hys⟩ := hm
      constructor
      · intro he
        have hc : coeffDecode d xs = coeffDecode d ys := by simpa using he
        exact congrArg Encodable.encode ((coeff_inj d xs ys hxs hys).mp hc)
      · intro he
        rw [he]
  | succ h ih =>
      intro n m hn hm
      obtain ⟨es, rfl, hes, hkeysEs⟩ := hn
      obtain ⟨fs, rfl, hfs, hkeysFs⟩ := hm
      constructor
      · intro he
        have hinj : Set.InjOn (formDecode d h) {k | CodeCanonical d h k} := by
          intro a ha b hb hab
          exact (ih a b ha hb).mp hab
        have hmap : Finsupp.mapDomain (formDecode d h) (mapDecode d es) =
            Finsupp.mapDomain (formDecode d h) (mapDecode d fs) := by
          simpa only [formDecode_succ_encode, entriesDecode_mapDomain] using he
        have hraw : mapDecode d es = mapDecode d fs :=
          (Finsupp.mapDomain_injOn {k | CodeCanonical d h k} hinj)
            (support_canonical_keys d h es hkeysEs)
            (support_canonical_keys d h fs hkeysFs) hmap
        exact congrArg Encodable.encode (map_inj es fs hes hfs hraw)
      · intro he
        rw [he]

theorem fixedPoints : Comparators.ExponentialHereditaryCodec.FixedPoints := by
  intro d h n hn
  exact (faithfulness d h _ n (canonicalization d h n).1 hn).mp
    (canonicalization d h n).2

theorem canonical_encode_normalizeMap (d h : Nat) (es : MapCode)
    (hkeys : ∀ e ∈ es, CodeCanonical d h e.1) :
    CodeCanonical d (h + 1) (Encodable.encode (normalizeMap d es)) := by
  refine ⟨normalizeMap d es, rfl, normalize_canonical d es, ?_⟩
  intro e he
  obtain ⟨a, ha, hkey⟩ := normalizeMap_key_mem d es e he
  rw [hkey]
  exact hkeys a ha

def coeffEncode {d : Nat} (a : Affine d) : CoeffCode := List.ofFn a

@[simp] theorem coeffEncode_canonical {d : Nat} (a : Affine d) :
    CoeffCanonical d (coeffEncode a) := by
  simp [CoeffCanonical, coeffEncode]

@[simp] theorem coeffEncode_decode {d : Nat} (a : Affine d) :
    coeffDecode d (coeffEncode a) = a := by
  funext i
  change (List.ofFn a).getD i.val 0 = a i
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]

theorem coverage : Comparators.ExponentialHereditaryCodec.Coverage := by
  classical
  intro d h
  induction h with
  | zero =>
      intro f
      exact ⟨Encodable.encode (coeffEncode f),
        ⟨coeffEncode f, rfl, coeffEncode_canonical f⟩,
        by simpa using coeffEncode_decode f⟩
  | succ h ih =>
      intro f
      let keyCode : Form d h → Nat := fun key => Classical.choose (ih key)
      have hkeyCanon (key : Form d h) : CodeCanonical d h (keyCode key) :=
        (Classical.choose_spec (ih key)).1
      have hkeyDecode (key : Form d h) : formDecode d h (keyCode key) = key :=
        (Classical.choose_spec (ih key)).2
      let raw : MapCode := f.support.toList.map
        (fun key => (keyCode key, coeffEncode (f key)))
      refine ⟨Encodable.encode (normalizeMap d raw),
        canonical_encode_normalizeMap d h raw ?_, ?_⟩
      · intro e he
        obtain ⟨key, _, rfl⟩ := List.mem_map.mp he
        exact hkeyCanon key
      · rw [formDecode_succ_encode, entriesDecode_normalizeMap]
        calc
          entriesDecode d h raw =
              (f.support.toList.map (fun key => Finsupp.single key (f key))).sum := by
            simp [entriesDecode, raw, List.foldr_map, List.sum_eq_foldr, hkeyDecode]
          _ = f.support.sum (fun key => Finsupp.single key (f key)) :=
            Finset.sum_map_toList _ _
          _ = f := Finsupp.sum_single f

theorem zeroCode_canonical (d h : Nat) : CodeCanonical d h (zeroCode d h) := by
  cases h with
  | zero => exact ⟨coeffConstant d 0, rfl, canon_constant d 0⟩
  | succ h =>
      refine ⟨[], rfl, ?_, ?_⟩
      · simp [MapCanonical]
      · simp

@[simp] theorem zeroCode_decode (d h : Nat) :
    formDecode d h (zeroCode d h) = zeroForm h := by
  cases h with
  | zero => simp [zeroCode, zeroForm, decode_constant, affConst_zero_eq]
  | succ h =>
      change formDecode d (h + 1) (Encodable.encode ([] : MapCode)) = 0
      rw [formDecode_succ_encode]
      rfl

theorem constantCode_canonical (d h n : Nat) : CodeCanonical d h (constantCode d h n) := by
  cases h with
  | zero => exact ⟨coeffConstant d n, rfl, canon_constant d n⟩
  | succ h =>
      apply canonical_encode_normalizeMap
      intro e he
      simp only [List.mem_singleton] at he
      subst e
      exact zeroCode_canonical d h

@[simp] theorem constantCode_decode (d h n : Nat) :
    formDecode d h (constantCode d h n) = constantForm h n := by
  cases h with
  | zero => simp [constantCode, constantForm, decode_constant]
  | succ h =>
      change formDecode d (h + 1) (Encodable.encode
        (normalizeMap d [(zeroCode d h, coeffConstant d n)])) = _
      rw [formDecode_succ_encode, entriesDecode_normalizeMap]
      simp [entriesDecode, decode_constant, constantForm]

theorem zeroAndConstants : Comparators.ExponentialHereditaryCodec.ZeroAndConstants :=
  fun d h n => ⟨zeroCode_canonical d h, zeroCode_decode d h,
    constantCode_canonical d h n, constantCode_decode d h n⟩

theorem pr_parseCoefficients : Primrec parseCoefficients :=
  Primrec.option_getD.comp (Primrec.decode (α := CoeffCode)) (Primrec.const [])

theorem pr_parseEntries : Primrec parseEntries :=
  Primrec.option_getD.comp (Primrec.decode (α := MapCode)) (Primrec.const [])

def rekeyEntries (es : MapCode) (rs : List Nat) : MapCode :=
  (List.range es.length).map (fun i => (rs.getD i 0, (es.getD i (0, [])).2))

theorem pr_rekeyEntries :
    Primrec (fun p : MapCode × List Nat => rekeyEntries p.1 p.2) := by
  unfold rekeyEntries
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
  exact (((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd).pair
    (Primrec.snd.comp ((Primrec.list_getD (0, ([] : CoeffCode))).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂

theorem rekeyEntries_map (es : MapCode) (F : Nat × CoeffCode → Nat) :
    rekeyEntries es (es.map F) = es.map (fun e => (F e, e.2)) := by
  apply List.ext_getElem
  · simp [rekeyEntries]
  · intro i hleft hright
    have hi : i < es.length := by simpa using hright
    simp [rekeyEntries, hi]

theorem pr_canonicalize :
    Primrec (fun p : Nat × Nat × Nat => canonicalize p.1 p.2.1 p.2.2) := by
  let f : Nat × Nat × Nat → Nat := fun p => canonicalize p.1 p.2.1 p.2.2
  let children : Nat × Nat × Nat → List (Nat × Nat × Nat) := fun p =>
    if p.2.1 = 0 then [] else
      (parseEntries p.2.2).map (fun e => (p.1, p.2.1 - 1, e.1))
  let assemble : Nat × Nat × Nat → List Nat → Option Nat := fun p rs =>
    some (if p.2.1 = 0 then
      Encodable.encode (coeffNormalize p.1 (parseCoefficients p.2.2))
    else Encodable.encode (normalizeMap p.1 (rekeyEntries (parseEntries p.2.2) rs)))
  have hd : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hh : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hchildren : Primrec children := by
    apply Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) (Primrec.const [])
    apply Primrec.list_map (pr_parseEntries.comp hn)
    exact ((hd.comp Primrec.fst).pair
      ((Primrec.nat_sub.comp (hh.comp Primrec.fst) (Primrec.const 1)).pair
        (Primrec.fst.comp Primrec.snd))).to₂
  have hbase : Primrec (fun p : Nat × Nat × Nat =>
      Encodable.encode (coeffNormalize p.1 (parseCoefficients p.2.2))) :=
    Primrec.encode.comp (pr_normalize.comp (hd.pair (pr_parseCoefficients.comp hn)))
  have hassemble : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite ((Primrec.eq.comp hh (Primrec.const 0)).comp Primrec.fst)
      (hbase.comp Primrec.fst)
    exact Primrec.encode.comp (pr_normalizeMap.comp ((hd.comp Primrec.fst).pair
      (pr_rekeyEntries.comp ((pr_parseEntries.comp (hn.comp Primrec.fst)).pair Primrec.snd))))
  apply Primrec.nat_omega_rec' f hh hchildren hassemble
  · intro p q hq
    by_cases h0 : p.2.1 = 0
    · simp [children, h0] at hq
    · have hMap : q ∈ (parseEntries p.2.2).map
          (fun e => (p.1, p.2.1 - 1, e.1)) := by
        simpa only [children, if_neg h0] using hq
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hMap
      dsimp
      omega
  · rintro ⟨d, h, n⟩
    cases h with
    | zero => rfl
    | succ h => simp [children, assemble, f, canonicalize, List.map_map, rekeyEntries_map]

theorem pr_zeroCode : Primrec (fun p : Nat × Nat => zeroCode p.1 p.2) := by
  have hbase : Primrec (fun p : Nat × Nat => Encodable.encode (coeffConstant p.1 0)) :=
    Primrec.encode.comp (pr_constant.comp (Primrec.fst.pair (Primrec.const 0)))
  apply (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    hbase (Primrec.const (Encodable.encode ([] : MapCode)))).of_eq
  rintro ⟨d, h⟩
  cases h <;> rfl

theorem pr_constantCode :
    Primrec (fun p : Nat × Nat × Nat => constantCode p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hh : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hcoeff := pr_constant.comp (hd.pair hn)
  have hzero := pr_zeroCode.comp (hd.pair (Primrec.nat_sub.comp hh (Primrec.const 1)))
  have hsucc := Primrec.encode.comp (pr_normalizeMap.comp (hd.pair
    (Primrec.list_cons.comp (hzero.pair hcoeff) (Primrec.const []))))
  apply (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0))
    (Primrec.encode.comp hcoeff) hsucc).of_eq
  rintro ⟨d, h, n⟩
  cases h <;> rfl

theorem hereditaryCodec : Comparators.ExponentialHereditaryCodec.Target :=
  ⟨canonicalization, faithfulness, fixedPoints, coverage, zeroAndConstants,
    pr_canonicalize, pr_zeroCode, pr_constantCode⟩

end LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof

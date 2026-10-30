module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodec
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Canonical numeric-key finite-map codes for paper-02 normal forms

Proves the frozen `Comparators.ExponentialNormalFormCodec.Target`: exact
coefficient denotations and fixed-length canonicality, faithful and canonical
map normalization with injectivity on canonical codes, and genuine `Primrec`
certificates for every executable list/natural-number operation. Hereditary
keys and the full term compiler are separate later obligations.
-/

namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof

open LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec
open LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodec

/-! ## Fixed-length coefficient vectors -/

theorem getD_map_range (n : Nat) (F : Nat → Nat) {i : Nat} (hi : i < n) :
    ((List.range n).map F).getD i 0 = F i := by
  have hl : i < ((List.range n).map F).length := by simp [hi]
  rw [List.getD_eq_getElem _ _ hl]
  simp

theorem decode_map_range (d : Nat) (F : Nat → Nat) (i : Fin (d + 1)) :
    coeffDecode d ((List.range (d + 1)).map F) i = F i.val :=
  getD_map_range (d + 1) F i.isLt

theorem canon_map (d : Nat) (F : Nat → Nat) : CoeffCanonical d ((List.range (d + 1)).map F) := by
  show ((List.range (d + 1)).map F).length = d + 1
  simp

theorem canon_normalize (d : Nat) (xs : CoeffCode) : CoeffCanonical d (coeffNormalize d xs) :=
  canon_map d (fun i => xs.getD i 0)

theorem canon_constant (d n : Nat) : CoeffCanonical d (coeffConstant d n) :=
  canon_map d (fun i => if i = 0 then n else 0)

theorem canon_variable (d i : Nat) : CoeffCanonical d (coeffVariable d i) :=
  canon_map d (fun j => if j = i + 1 then 1 else 0)

theorem canon_add (d : Nat) (xs ys : CoeffCode) : CoeffCanonical d (coeffAdd d xs ys) :=
  canon_map d (fun i => xs.getD i 0 + ys.getD i 0)

theorem canon_scale (d k : Nat) (xs : CoeffCode) : CoeffCanonical d (coeffScale d k xs) :=
  canon_map d (fun i => k * xs.getD i 0)

theorem canon_remove (d : Nat) (xs : CoeffCode) : CoeffCanonical d (coeffRemove d xs) :=
  canon_map d (fun i => if i = 0 then 0 else xs.getD i 0)

theorem coeff_inj (d : Nat) (xs ys : CoeffCode) (hx : CoeffCanonical d xs)
    (hy : CoeffCanonical d ys) : coeffDecode d xs = coeffDecode d ys ↔ xs = ys := by
  have hx' : xs.length = d + 1 := hx
  have hy' : ys.length = d + 1 := hy
  constructor
  · intro h
    apply List.ext_getElem
    · rw [hx', hy']
    · intro n h1 h2
      have hn : n < d + 1 := by rw [← hx']; exact h1
      have e : xs.getD n 0 = ys.getD n 0 := congrFun h ⟨n, hn⟩
      rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e
  · intro h
    rw [h]

theorem affConst_zero_eq (d : Nat) : affineConstant (d := d) 0 = 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [affineConstant]

theorem decode_normalize (d : Nat) (xs : CoeffCode) :
    coeffDecode d (coeffNormalize d xs) = coeffDecode d xs := by
  funext i
  exact decode_map_range d (fun j => xs.getD j 0) i

theorem decode_constant (d n : Nat) : coeffDecode d (coeffConstant d n) = affineConstant n := by
  funext i
  show coeffDecode d ((List.range (d + 1)).map (fun j => if j = 0 then n else 0)) i = _
  rw [decode_map_range]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [affineConstant]
  · simp [affineConstant]

theorem decode_add (d : Nat) (xs ys : CoeffCode) :
    coeffDecode d (coeffAdd d xs ys) = coeffDecode d xs + coeffDecode d ys := by
  funext i
  exact decode_map_range d (fun j => xs.getD j 0 + ys.getD j 0) i

theorem decode_scale (d k : Nat) (xs : CoeffCode) :
    coeffDecode d (coeffScale d k xs) = (fun i => k * coeffDecode d xs i) := by
  funext i
  exact decode_map_range d (fun j => k * xs.getD j 0) i

theorem decode_remove (d : Nat) (xs : CoeffCode) :
    coeffDecode d (coeffRemove d xs) = affineRemoveConstant (coeffDecode d xs) := by
  funext i
  show coeffDecode d ((List.range (d + 1)).map
    (fun j => if j = 0 then 0 else xs.getD j 0)) i = _
  rw [decode_map_range]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [affineRemoveConstant]
  · simp [affineRemoveConstant, coeffDecode]

theorem decode_variable (d : Nat) (i : Fin d) :
    coeffDecode d (coeffVariable d i.val) = Fin.cases 0 (fun j => if j = i then 1 else 0) := by
  funext k
  show coeffDecode d ((List.range (d + 1)).map
    (fun j => if j = i.val + 1 then 1 else 0)) k = _
  rw [decode_map_range]
  refine Fin.cases ?_ (fun j => ?_) k
  · have h0 : (0 : Nat) ≠ i.val + 1 := by omega
    simp [h0]
  · by_cases hj : j = i
    · subst hj
      simp
    · have hv : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp [hj, hv]

theorem isZero_iff (d : Nat) (xs : CoeffCode) :
    coeffIsZero d xs = true ↔ coeffDecode d xs = 0 := by
  unfold coeffIsZero
  rw [decide_eq_true_eq,
    ← coeff_inj d (coeffNormalize d xs) (coeffConstant d 0) (canon_normalize d xs)
      (canon_constant d 0),
    decode_normalize, decode_constant, affConst_zero_eq]

theorem isZero_normalize (d : Nat) (xs : CoeffCode) :
    coeffIsZero d (coeffNormalize d xs) = coeffIsZero d xs := by
  rw [Bool.eq_iff_iff, isZero_iff, isZero_iff, decode_normalize]

theorem decode_ne_zero {d : Nat} {a : CoeffCode} (h : coeffIsZero d a = false) :
    coeffDecode d a ≠ 0 := by
  intro h0
  have h1 := (isZero_iff d a).mpr h0
  rw [h] at h1
  cases h1

theorem coeffIsZero_add {d : Nat} {c a : CoeffCode} (hc : coeffIsZero d c = false) :
    coeffIsZero d (coeffAdd d c a) = false := by
  cases h : coeffIsZero d (coeffAdd d c a)
  · rfl
  · exfalso
    have h1 := (isZero_iff d _).mp h
    rw [decode_add] at h1
    have h2 : coeffDecode d c = 0 := by
      funext i
      have h3 := congrFun h1 i
      change coeffDecode d c i + coeffDecode d a i = 0 at h3
      change coeffDecode d c i = 0
      omega
    exact decode_ne_zero hc h2

theorem coefficientSemantics : CoefficientSemantics := by
  intro d xs ys k n
  exact ⟨decode_normalize d xs, decode_constant d n, decode_add d xs ys, decode_scale d k xs,
    decode_remove d xs, isZero_iff d xs, fun i => decode_variable d i⟩

theorem coefficientCanonicality : CoefficientCanonicality :=
  ⟨fun d xs ys hx hy => coeff_inj d xs ys hx hy,
    fun d xs ys k n i => ⟨canon_normalize d xs, canon_constant d n, canon_add d xs ys,
      canon_scale d k xs, canon_remove d xs, canon_variable d i⟩⟩

/-! ## Map denotation of insertion and normalization -/

theorem decode_insertRaw (d key : Nat) (c : CoeffCode) : ∀ es : MapCode,
    mapDecode d (insertRaw d key c es) =
      Finsupp.single key (coeffDecode d c) + mapDecode d es
  | [] => rfl
  | (j, a) :: rest => by
      show mapDecode d (if key < j then (key, c) :: (j, a) :: rest
          else if key = j then (key, coeffAdd d c a) :: rest
          else (j, a) :: insertRaw d key c rest) =
        Finsupp.single key (coeffDecode d c) +
          (Finsupp.single j (coeffDecode d a) + mapDecode d rest)
      by_cases h1 : key < j
      · rw [if_pos h1]
        rfl
      · rw [if_neg h1]
        by_cases h2 : key = j
        · rw [if_pos h2, ← h2]
          show Finsupp.single key (coeffDecode d (coeffAdd d c a)) + mapDecode d rest =
            Finsupp.single key (coeffDecode d c) +
              (Finsupp.single key (coeffDecode d a) + mapDecode d rest)
          rw [decode_add, Finsupp.single_add, add_assoc]
        · rw [if_neg h2]
          show Finsupp.single j (coeffDecode d a) + mapDecode d (insertRaw d key c rest) = _
          rw [decode_insertRaw d key c rest, add_left_comm]

theorem decode_insertEntry (d key : Nat) (c : CoeffCode) (es : MapCode) :
    mapDecode d (insertEntry d key c es) =
      Finsupp.single key (coeffDecode d c) + mapDecode d es := by
  unfold insertEntry
  by_cases hz : coeffIsZero d c = true
  · rw [if_pos hz, (isZero_iff d c).mp hz, Finsupp.single_zero, zero_add]
  · rw [if_neg hz, decode_insertRaw, decode_normalize]

theorem decode_normalizeMap (d : Nat) : ∀ es : MapCode,
    mapDecode d (normalizeMap d es) = mapDecode d es
  | [] => rfl
  | e :: es => by
      show mapDecode d (insertEntry d e.1 e.2 (normalizeMap d es)) =
        Finsupp.single e.1 (coeffDecode d e.2) + mapDecode d es
      rw [decode_insertEntry, decode_normalizeMap d es]

/-! ## Canonicality of insertion and normalization -/

theorem canon_cons {d j : Nat} {a : CoeffCode} {rest : MapCode}
    (h : MapCanonical d ((j, a) :: rest)) :
    (∀ e ∈ rest, j < e.1) ∧ rest.Pairwise (fun x y => x.1 < y.1) ∧
      (∀ e ∈ rest, CoeffCanonical d e.2 ∧ coeffIsZero d e.2 = false) ∧
      CoeffCanonical d a ∧ coeffIsZero d a = false := by
  obtain ⟨hp, he⟩ := h
  rw [List.pairwise_cons] at hp
  obtain ⟨hlt, hp'⟩ := hp
  obtain ⟨hca, hza⟩ := he (j, a) (List.mem_cons.mpr (Or.inl rfl))
  exact ⟨hlt, hp', fun e hm => he e (List.mem_cons.mpr (Or.inr hm)), hca, hza⟩

theorem insertRaw_mem {d key : Nat} {c : CoeffCode} : ∀ (es : MapCode) (e : Nat × CoeffCode),
    e ∈ insertRaw d key c es → e.1 = key ∨ e ∈ es
  | [], e, he => by
      change e ∈ [(key, c)] at he
      rw [List.mem_singleton.mp he]
      exact Or.inl rfl
  | (j, a) :: rest, e, he => by
      change e ∈ (if key < j then (key, c) :: (j, a) :: rest
        else if key = j then (key, coeffAdd d c a) :: rest
        else (j, a) :: insertRaw d key c rest) at he
      by_cases h1 : key < j
      · rw [if_pos h1] at he
        rcases List.mem_cons.mp he with h | h
        · exact Or.inl (by subst h; rfl)
        · exact Or.inr h
      · rw [if_neg h1] at he
        by_cases h2 : key = j
        · rw [if_pos h2] at he
          rcases List.mem_cons.mp he with h | h
          · exact Or.inl (by subst h; rfl)
          · exact Or.inr (List.mem_cons.mpr (Or.inr h))
        · rw [if_neg h2] at he
          rcases List.mem_cons.mp he with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · rcases insertRaw_mem rest e h with h' | h'
            · exact Or.inl h'
            · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem insertRaw_canonical {d key : Nat} {c : CoeffCode} (hc : CoeffCanonical d c)
    (hz : coeffIsZero d c = false) : ∀ es : MapCode, MapCanonical d es →
      MapCanonical d (insertRaw d key c es)
  | [], _ => by
      show MapCanonical d [(key, c)]
      refine ⟨List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil, ?_⟩
      intro e he
      rw [List.mem_singleton.mp he]
      exact ⟨hc, hz⟩
  | (j, a) :: rest, hes => by
      obtain ⟨hj, hp, hent, hca, hza⟩ := canon_cons hes
      show MapCanonical d (if key < j then (key, c) :: (j, a) :: rest
        else if key = j then (key, coeffAdd d c a) :: rest
        else (j, a) :: insertRaw d key c rest)
      by_cases h1 : key < j
      · rw [if_pos h1]
        refine ⟨List.Pairwise.cons ?_ (List.Pairwise.cons hj hp), ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with h | h
          · subst h
            exact h1
          · have := hj e h
            show key < e.1
            omega
        · intro e he
          rcases List.mem_cons.mp he with h | h
          · subst h
            exact ⟨hc, hz⟩
          · rcases List.mem_cons.mp h with h' | h'
            · subst h'
              exact ⟨hca, hza⟩
            · exact hent e h'
      · rw [if_neg h1]
        by_cases h2 : key = j
        · rw [if_pos h2]
          refine ⟨List.Pairwise.cons ?_ hp, ?_⟩
          · intro e he
            have := hj e he
            show key < e.1
            omega
          · intro e he
            rcases List.mem_cons.mp he with h | h
            · subst h
              exact ⟨canon_add d c a, coeffIsZero_add hz⟩
            · exact hent e h
        · rw [if_neg h2]
          obtain ⟨ihp, ihe⟩ := insertRaw_canonical hc hz rest ⟨hp, hent⟩
          refine ⟨List.Pairwise.cons ?_ ihp, ?_⟩
          · intro e he
            rcases insertRaw_mem rest e he with h | h
            · show j < e.1
              omega
            · exact hj e h
          · intro e he
            rcases List.mem_cons.mp he with h | h
            · subst h
              exact ⟨hca, hza⟩
            · exact ihe e h

theorem insertEntry_canonical {d : Nat} (key : Nat) (c : CoeffCode) {es : MapCode}
    (hes : MapCanonical d es) : MapCanonical d (insertEntry d key c es) := by
  unfold insertEntry
  by_cases hz : coeffIsZero d c = true
  · rw [if_pos hz]
    exact hes
  · rw [if_neg hz]
    have hz' : coeffIsZero d c = false := by
      cases h : coeffIsZero d c
      · rfl
      · exact absurd h hz
    exact insertRaw_canonical (canon_normalize d c)
      (by rw [isZero_normalize]; exact hz') es hes

theorem normalize_canonical (d : Nat) : ∀ es : MapCode, MapCanonical d (normalizeMap d es)
  | [] => ⟨List.Pairwise.nil, fun e (he : e ∈ ([] : MapCode)) => by cases he⟩
  | e :: es => insertEntry_canonical e.1 e.2 (normalize_canonical d es)

/-! ## Injectivity on canonical map codes -/

theorem eval_absent {d k : Nat} : ∀ (es : MapCode), (∀ e ∈ es, e.1 ≠ k) →
    mapDecode d es k = 0
  | [], _ => rfl
  | e :: es, h => by
      have h1 : e.1 ≠ k := h e (List.mem_cons.mpr (Or.inl rfl))
      have h2 := eval_absent (d := d) es (fun e' he' => h e' (List.mem_cons.mpr (Or.inr he')))
      show (Finsupp.single e.1 (coeffDecode d e.2) + mapDecode d es) k = 0
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm h1), h2, add_zero]

theorem head_eval {d j : Nat} {a : CoeffCode} {rest : MapCode} (h : ∀ e ∈ rest, j < e.1) :
    mapDecode d ((j, a) :: rest) j = coeffDecode d a := by
  show (Finsupp.single j (coeffDecode d a) + mapDecode d rest) j = coeffDecode d a
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    eval_absent (d := d) (k := j) rest (fun e he => by have := h e he; omega), add_zero]

theorem map_inj {d : Nat} : ∀ (es fs : MapCode), MapCanonical d es → MapCanonical d fs →
    mapDecode d es = mapDecode d fs → es = fs
  | [], [], _, _, _ => rfl
  | [], (k, b) :: fs, _, hf, heq => by
      exfalso
      obtain ⟨hk, _, _, _, hzb⟩ := canon_cons hf
      have h1 := head_eval (d := d) (a := b) hk
      rw [← heq] at h1
      exact decode_ne_zero hzb h1.symm
  | (j, a) :: es, [], he, _, heq => by
      exfalso
      obtain ⟨hj, _, _, _, hza⟩ := canon_cons he
      have h1 := head_eval (d := d) (a := a) hj
      rw [heq] at h1
      exact decode_ne_zero hza h1.symm
  | (j, a) :: es, (k, b) :: fs, he, hf, heq => by
      obtain ⟨hj, hpe, hee, hca, hza⟩ := canon_cons he
      obtain ⟨hk, hpf, hef, hcb, hzb⟩ := canon_cons hf
      have hjk : j = k := by
        rcases Nat.lt_trichotomy j k with hlt | hEq | hgt
        · exfalso
          have h1 := head_eval (d := d) (a := a) hj
          rw [heq] at h1
          have h2 : mapDecode d ((k, b) :: fs) j = 0 :=
            eval_absent (d := d) (k := j) ((k, b) :: fs) (fun e hmem => by
              rcases List.mem_cons.mp hmem with h | h
              · subst h
                show k ≠ j
                omega
              · have := hk e h
                omega)
          exact decode_ne_zero hza (h1.symm.trans h2)
        · exact hEq
        · exfalso
          have h1 := head_eval (d := d) (a := b) hk
          rw [← heq] at h1
          have h2 : mapDecode d ((j, a) :: es) k = 0 :=
            eval_absent (d := d) (k := k) ((j, a) :: es) (fun e hmem => by
              rcases List.mem_cons.mp hmem with h | h
              · subst h
                show j ≠ k
                omega
              · have := hj e h
                omega)
          exact decode_ne_zero hzb (h1.symm.trans h2)
      have hdec : coeffDecode d a = coeffDecode d b := by
        have h1 := head_eval (d := d) (a := a) hj
        rw [heq, hjk, head_eval hk] at h1
        exact h1.symm
      have hab : a = b := (coeff_inj d a b hca hcb).mp hdec
      have htail : mapDecode d es = mapDecode d fs := by
        apply Finsupp.ext
        intro x
        funext i
        have hx : (Finsupp.single j (coeffDecode d a) + mapDecode d es) x i =
            (Finsupp.single k (coeffDecode d b) + mapDecode d fs) x i :=
          congrFun (DFunLike.congr_fun heq x) i
        rw [Finsupp.add_apply, Finsupp.add_apply, Pi.add_apply, Pi.add_apply, hjk, hdec] at hx
        omega
      rw [hjk, hab, map_inj es fs ⟨hpe, hee⟩ ⟨hpf, hef⟩ htail]

theorem canonicalMapRepresentation : CanonicalMapRepresentation :=
  ⟨fun d es => ⟨normalize_canonical d es, decode_normalizeMap d es⟩,
    fun d es fs he hf => ⟨map_inj es fs he hf, fun h => by rw [h]⟩⟩

/-! ## Genuine primitive recursion -/

theorem pr_rangeMap {α : Type*} [Primcodable α] {n : α → Nat} {F : α → Nat → Nat}
    (hn : Primrec n) (hF : Primrec₂ F) :
    Primrec (fun a => (List.range (n a + 1)).map (F a)) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hn (Primrec.const 1))) hF

theorem pr_normalize : Primrec (fun p : Nat × CoeffCode => coeffNormalize p.1 p.2) := by
  have hF : Primrec₂ (fun (p : Nat × CoeffCode) (i : Nat) => p.2.getD i 0) :=
    (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (pr_rangeMap Primrec.fst hF).of_eq fun p => rfl

theorem pr_constant : Primrec (fun p : Nat × Nat => coeffConstant p.1 p.2) := by
  have hc : PrimrecPred (fun q : (Nat × Nat) × Nat => q.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hF : Primrec₂ (fun (p : Nat × Nat) (i : Nat) => if i = 0 then p.2 else 0) :=
    Primrec.ite hc (Primrec.snd.comp Primrec.fst) (Primrec.const 0)
  exact (pr_rangeMap Primrec.fst hF).of_eq fun p => rfl

theorem pr_variable : Primrec (fun p : Nat × Nat => coeffVariable p.1 p.2) := by
  have hc : PrimrecPred (fun q : (Nat × Nat) × Nat => q.2 = q.1.2 + 1) :=
    Primrec.eq.comp Primrec.snd
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
  have hF : Primrec₂ (fun (p : Nat × Nat) (j : Nat) => if j = p.2 + 1 then 1 else 0) :=
    Primrec.ite hc (Primrec.const 1) (Primrec.const 0)
  exact (pr_rangeMap Primrec.fst hF).of_eq fun p => rfl

theorem pr_add : Primrec (fun p : Nat × CoeffCode × CoeffCode => coeffAdd p.1 p.2.1 p.2.2) := by
  have hF : Primrec₂ (fun (p : Nat × CoeffCode × CoeffCode) (i : Nat) =>
      p.2.1.getD i 0 + p.2.2.getD i 0) :=
    Primrec.nat_add.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  exact (pr_rangeMap Primrec.fst hF).of_eq fun p => rfl

theorem pr_scale : Primrec (fun p : Nat × Nat × CoeffCode => coeffScale p.1 p.2.1 p.2.2) := by
  have hF : Primrec₂ (fun (p : Nat × Nat × CoeffCode) (i : Nat) => p.2.1 * p.2.2.getD i 0) :=
    Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  exact (pr_rangeMap Primrec.fst hF).of_eq fun p => rfl

theorem pr_remove : Primrec (fun p : Nat × CoeffCode => coeffRemove p.1 p.2) := by
  have hc : PrimrecPred (fun q : (Nat × CoeffCode) × Nat => q.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hF : Primrec₂ (fun (p : Nat × CoeffCode) (i : Nat) =>
      if i = 0 then 0 else p.2.getD i 0) :=
    Primrec.ite hc (Primrec.const 0)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (pr_rangeMap Primrec.fst hF).of_eq fun p => rfl

theorem pr_isZero : Primrec (fun p : Nat × CoeffCode => coeffIsZero p.1 p.2) := by
  have h : PrimrecPred (fun p : Nat × CoeffCode =>
      coeffNormalize p.1 p.2 = coeffConstant p.1 0) :=
    Primrec.eq.comp pr_normalize (pr_constant.comp (Primrec.fst.pair (Primrec.const 0)))
  exact h.decide.of_eq fun p => rfl

/-- One step of the list recursion computing `insertRaw`. -/
def rawStep (a : (Nat × Nat × CoeffCode) × MapCode)
    (s : (Nat × CoeffCode) × MapCode × MapCode) : MapCode :=
  if a.1.2.1 < s.1.1 then (a.1.2.1, a.1.2.2) :: s.1 :: s.2.1
  else if a.1.2.1 = s.1.1 then (a.1.2.1, coeffAdd a.1.1 a.1.2.2 s.1.2) :: s.2.1
  else s.1 :: s.2.2

abbrev RawIn := ((Nat × Nat × CoeffCode) × MapCode) × ((Nat × CoeffCode) × MapCode × MapCode)

theorem pr_rawStep : Primrec₂ rawStep := by
  have pd : Primrec (fun r : RawIn => r.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have pk : Primrec (fun r : RawIn => r.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have pc : Primrec (fun r : RawIn => r.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have pb : Primrec (fun r : RawIn => r.2.1) := Primrec.fst.comp Primrec.snd
  have pl : Primrec (fun r : RawIn => r.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have pih : Primrec (fun r : RawIn => r.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have pj : Primrec (fun r : RawIn => r.2.1.1) := Primrec.fst.comp pb
  have px : Primrec (fun r : RawIn => r.2.1.2) := Primrec.snd.comp pb
  have c1 : PrimrecPred (fun r : RawIn => r.1.1.2.1 < r.2.1.1) := Primrec.nat_lt.comp pk pj
  have c2 : PrimrecPred (fun r : RawIn => r.1.1.2.1 = r.2.1.1) := Primrec.eq.comp pk pj
  have b1 : Primrec (fun r : RawIn => (r.1.1.2.1, r.1.1.2.2) :: r.2.1 :: r.2.2.1) :=
    Primrec.list_cons.comp (pk.pair pc) (Primrec.list_cons.comp pb pl)
  have b2 : Primrec (fun r : RawIn =>
      (r.1.1.2.1, coeffAdd r.1.1.1 r.1.1.2.2 r.2.1.2) :: r.2.2.1) :=
    Primrec.list_cons.comp (pk.pair (pr_add.comp (pd.pair (pc.pair px)))) pl
  have b3 : Primrec (fun r : RawIn => r.2.1 :: r.2.2.2) := Primrec.list_cons.comp pb pih
  refine Primrec.of_eq (Primrec.ite c1 b1 (Primrec.ite c2 b2 b3)) ?_
  intro r
  rfl

theorem insertRaw_rec (t : Nat × Nat × CoeffCode) (es₀ : MapCode) : ∀ es : MapCode,
    List.recOn (motive := fun _ => MapCode) es [(t.2.1, t.2.2)]
      (fun b l IH => rawStep (t, es₀) (b, l, IH)) = insertRaw t.1 t.2.1 t.2.2 es
  | [] => rfl
  | (j, x) :: rest =>
      congrArg (fun r => rawStep (t, es₀) ((j, x), rest, r)) (insertRaw_rec t es₀ rest)

theorem pr_insertRaw : Primrec (fun a : (Nat × Nat × CoeffCode) × MapCode =>
    insertRaw a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  have hg : Primrec (fun a : (Nat × Nat × CoeffCode) × MapCode => [(a.1.2.1, a.1.2.2)]) :=
    Primrec.list_cons.comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const [])
  refine Primrec.of_eq (Primrec.list_rec Primrec.snd hg pr_rawStep) ?_
  intro a
  exact insertRaw_rec a.1 a.2 a.2

theorem pr_insertEntry : Primrec (fun p : Nat × Nat × CoeffCode × MapCode =>
    insertEntry p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hz : PrimrecPred (fun p : Nat × Nat × CoeffCode × MapCode =>
      coeffIsZero p.1 p.2.2.1 = true) :=
    Primrec.eq.comp
      (pr_isZero.comp (Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const true)
  have hr : Primrec (fun p : Nat × Nat × CoeffCode × MapCode =>
      insertRaw p.1 p.2.1 (coeffNormalize p.1 p.2.2.1) p.2.2.2) :=
    pr_insertRaw.comp ((Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (pr_normalize.comp (Primrec.fst.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  refine Primrec.of_eq (Primrec.ite hz (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hr) ?_
  intro p
  rfl

theorem pr_normalizeMap : Primrec (fun p : Nat × MapCode => normalizeMap p.1 p.2) := by
  have hh : Primrec₂ (fun (p : Nat × MapCode) (s : (Nat × CoeffCode) × MapCode) =>
      insertEntry p.1 s.1.1 s.1.2 s.2) :=
    pr_insertEntry.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))))
  refine Primrec.of_eq (Primrec.list_foldr Primrec.snd (Primrec.const []) hh) ?_
  intro p
  rfl

theorem actualPrimitiveRecursion : ActualPrimitiveRecursion :=
  ⟨pr_normalize, pr_constant, pr_variable, pr_add, pr_scale, pr_remove, pr_isZero,
    pr_insertEntry, pr_normalizeMap⟩

theorem normalFormCodec : Comparators.ExponentialNormalFormCodec.Target := by
  exact ⟨coefficientSemantics, coefficientCanonicality, canonicalMapRepresentation,
    actualPrimitiveRecursion⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof

module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWOrdinalPrefixCode
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Faithful original O prefix coding after independent target freeze. The
parser theorem is syntactic and does not decide denotational comparison. -/
namespace LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCodeProof

open PositiveExpression WWOrdinalTermSemantics WWOrdinalPrefixCode

private theorem binary_sound (d k tag : Nat) (ctor : Term (Fin d) → Term (Fin d) → Term (Fin d))
    (hc : ∀ a b, encode (ctor a b) = tag :: (encode a ++ encode b))
    (ih : ∀ (raw rest : List Nat) (t : Term (Fin d)), parse d k raw = some (t, rest) → raw = encode t ++ rest)
    (raw rest : List Nat) (t : Term (Fin d))
    (h : (do
      let (a, ys) ← parse d k raw
      let (b, zs) ← parse d k ys
      some (ctor a b, zs)) = some (t, rest)) : tag :: raw = encode t ++ rest := by
  cases ha : parse d k raw with
  | none => simp [ha] at h
  | some p =>
      rcases p with ⟨a, ys⟩
      cases hb : parse d k ys with
      | none => simp [ha, hb] at h
      | some q =>
          rcases q with ⟨b, zs⟩
          simp only [ha, hb, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rw [hc, ih raw ys a ha, ih ys zs b hb]
          simp only [List.cons_append, List.append_assoc]

theorem parsingSound : Comparators.WWOrdinalPrefixCode.ParsingSound := by
  intro d k
  induction k with
  | zero => intro raw rest t h; simp [parse] at h
  | succ k ih =>
      intro raw rest t h
      cases raw with
      | nil => simp [parse] at h
      | cons tag xs =>
          by_cases htag : tag ≤ 6
          · interval_cases tag
            · simp only [parse, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
            · cases xs with
              | nil => simp [parse] at h
              | cons i ys =>
                  by_cases hi : i < d
                  · simp only [parse, hi, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · simp [parse, hi] at h
            · exact binary_sound d k 2 Term.add (fun _ _ => rfl) ih xs rest t (by simpa only [parse] using h)
            · exact binary_sound d k 3 Term.emul (fun _ _ => rfl) ih xs rest t (by simpa only [parse] using h)
            · simp only [parse, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
            · simp only [parse, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
            · exact binary_sound d k 6 Term.collapse (fun _ _ => rfl) ih xs rest t (by simpa only [parse] using h)
          · have ht : 7 ≤ tag := by omega
            obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le ht
            have he : tag = n + 7 := by omega
            rw [he] at h
            simp [parse] at h

theorem parsingComplete : Comparators.WWOrdinalPrefixCode.ParsingComplete := by
  intro d t
  induction t with
  | var i =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k => simp [encode, parse, i.isLt]
  | zero =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k => rfl
  | one =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k => rfl
  | omega =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k => rfl
  | add a b ha hb =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hka : height a ≤ k := by simp only [height] at hk; omega
          have hkb : height b ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ha k hka, hb k hkb,
            bind, Option.bind_some]
  | emul a b ha hb =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hka : height a ≤ k := by simp only [height] at hk; omega
          have hkb : height b ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ha k hka, hb k hkb,
            bind, Option.bind_some]
  | collapse a b ha hb =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hka : height a ≤ k := by simp only [height] at hk; omega
          have hkb : height b ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ha k hka, hb k hkb,
            bind, Option.bind_some]

theorem finiteFuel : Comparators.WWOrdinalPrefixCode.FiniteFuel := by
  intro d t
  induction t <;> simp only [height, encode, List.length_cons, List.length_nil, List.length_append] <;> omega

theorem decoderExact : Comparators.WWOrdinalPrefixCode.DecoderExact := by
  intro d raw t
  constructor
  · intro h
    cases hp : parse d (raw.length + 1) raw with
    | none => simp [decode, hp] at h
    | some p =>
        rcases p with ⟨s, rest⟩
        by_cases hr : rest = []
        · subst rest
          simp only [decode, hp, bind, Option.bind_some, ↓reduceIte, Option.some.injEq] at h
          subst s
          simpa only [List.append_nil] using parsingSound d _ raw [] t hp
        · simp [decode, hp, hr] at h
  · intro h
    subst raw
    have hp := parsingComplete d t ((encode t).length + 1) (finiteFuel d t) []
    simp only [List.append_nil] at hp
    simp [decode, hp]

theorem encodingInjective : Comparators.WWOrdinalPrefixCode.EncodingInjective := by
  intro d a b h
  have ha := (decoderExact d (encode a) a).mpr rfl
  have hb := (decoderExact d (encode b) b).mpr rfl
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem embedCompatibility : Comparators.WWOrdinalPrefixCode.EmbedCompatibility := by
  intro d e
  induction e <;> simp_all [embed, encode, CircuitReduction.encodeExpr, Expr.rename]

theorem wwOrdinalPrefixCode : Comparators.WWOrdinalPrefixCode.Target :=
  ⟨parsingSound, parsingComplete, finiteFuel, decoderExact, encodingInjective, embedCompatibility⟩

end LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCodeProof

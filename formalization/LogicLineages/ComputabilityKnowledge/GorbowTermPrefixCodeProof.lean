module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermPrefixCode
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Faithful full-language term prefix coding after independent target freeze. The
parser theorem is syntactic and does not decide semantic truth. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof

open GorbowSyntax GorbowTermPrefixCode

private theorem binary_sound (d k tag : Nat) (ctor : Term d → Term d → Term d)
    (hc : ∀ a b, encode (ctor a b) = tag :: (encode a ++ encode b))
    (ih : ∀ (raw rest : List Nat) (t : Term d), parse d k raw = some (t, rest) → raw = encode t ++ rest)
    (raw rest : List Nat) (t : Term d)
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

private theorem unary_sound (d k tag : Nat) (ctor : Term d → Term d)
    (hc : ∀ a, encode (ctor a) = tag :: encode a)
    (ih : ∀ (raw rest : List Nat) (t : Term d), parse d k raw = some (t, rest) → raw = encode t ++ rest)
    (raw rest : List Nat) (t : Term d)
    (h : (do let (a, ys) ← parse d k raw; some (ctor a, ys)) = some (t, rest)) :
    tag :: raw = encode t ++ rest := by
  cases ha : parse d k raw with
  | none => simp [ha] at h
  | some p =>
      rcases p with ⟨a, ys⟩
      simp only [ha, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [hc, ih raw ys a ha]
      rfl

theorem parsingSound : Comparators.GorbowTermPrefixCode.ParsingSound := by
  intro d k
  induction k with
  | zero => intro raw rest t h; simp [parse] at h
  | succ k ih =>
      intro raw rest t h
      cases raw with
      | nil => simp [parse] at h
      | cons tag xs =>
          by_cases htag : tag ≤ 5
          · interval_cases tag
            · cases xs with
              | nil => simp [parse] at h
              | cons i ys =>
                  by_cases hi : i < d
                  · simp only [parse, hi, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at h
                    rcases h with ⟨rfl, rfl⟩
                    rfl
                  · simp [parse, hi] at h
            · simp only [parse, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
            · exact unary_sound d k 2 Term.succ (fun _ => rfl) ih xs rest t (by simpa only [parse] using h)
            · exact binary_sound d k 3 Term.add (fun _ _ => rfl) ih xs rest t (by simpa only [parse] using h)
            · exact binary_sound d k 4 Term.mul (fun _ _ => rfl) ih xs rest t (by simpa only [parse] using h)
            · exact unary_sound d k 5 Term.universalFunction (fun _ => rfl) ih xs rest t (by simpa only [parse] using h)
          · have ht : 6 ≤ tag := by omega
            obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le ht
            have he : tag = n + 6 := by omega
            rw [he] at h
            simp [parse] at h

theorem parsingComplete : Comparators.GorbowTermPrefixCode.ParsingComplete := by
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
  | succ a ha | universalFunction a ha =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hka : height a ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, parse, ha k hka, bind, Option.bind_some]
  | add a b ha hb | mul a b ha hb =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hka : height a ≤ k := by simp only [height] at hk; omega
          have hkb : height b ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ha k hka, hb k hkb,
            bind, Option.bind_some]

theorem finiteFuel : Comparators.GorbowTermPrefixCode.FiniteFuel := by
  intro d t
  induction t <;> simp only [height, encode, List.length_cons, List.length_nil, List.length_append] <;> omega

theorem decoderExact : Comparators.GorbowTermPrefixCode.DecoderExact := by
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

theorem encodingInjective : Comparators.GorbowTermPrefixCode.EncodingInjective := by
  intro d a b h
  have ha := (decoderExact d (encode a) a).mpr rfl
  have hb := (decoderExact d (encode b) b).mpr rfl
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem variableDomain : Comparators.GorbowTermPrefixCode.VariableDomain := by
  intro n i k rest h
  have hi : ¬ i < n := by omega
  simp [parse, hi]

theorem gorbowTermPrefixCode : Comparators.GorbowTermPrefixCode.Target :=
  ⟨parsingSound, parsingComplete, finiteFuel, decoderExact, encodingInjective, variableDomain⟩

end LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof

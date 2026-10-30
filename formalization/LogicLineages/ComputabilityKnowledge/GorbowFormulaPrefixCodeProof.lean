module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowFormulaPrefixCode
public import LogicLineages.ComputabilityKnowledge.GorbowTermPrefixCodeProof

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof
open GorbowSyntax GorbowFormulaPrefixCode

private theorem unary_sound {α : Type} (n tag : Nat) (enc : α → List Nat)
    (p : List Nat → Option (α × List Nat)) (ctor : α → Formula n)
    (hc : ∀ a, encode (ctor a) = tag :: enc a)
    (ih : ∀ raw rest a, p raw = some (a, rest) → raw = enc a ++ rest)
    (raw rest : List Nat) (φ : Formula n)
    (h : (do let (a, ys) ← p raw; some (ctor a, ys)) = some (φ, rest)) :
    tag :: raw = encode φ ++ rest := by
  cases ha : p raw with
  | none => simp [ha] at h
  | some q =>
      rcases q with ⟨a, ys⟩
      simp only [ha, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [hc, ih raw ys a ha]
      rfl

private theorem binary_sound {α : Type} (n tag : Nat) (enc : α → List Nat)
    (p : List Nat → Option (α × List Nat)) (ctor : α → α → Formula n)
    (hc : ∀ a b, encode (ctor a b) = tag :: (enc a ++ enc b))
    (ih : ∀ raw rest a, p raw = some (a, rest) → raw = enc a ++ rest)
    (raw rest : List Nat) (φ : Formula n)
    (h : (do let (a, ys) ← p raw; let (b, zs) ← p ys; some (ctor a b, zs)) = some (φ, rest)) :
    tag :: raw = encode φ ++ rest := by
  cases ha : p raw with
  | none => simp [ha] at h
  | some q =>
      rcases q with ⟨a, ys⟩
      cases hb : p ys with
      | none => simp [ha, hb] at h
      | some r =>
          rcases r with ⟨b, zs⟩
          simp only [ha, hb, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rw [hc, ih raw ys a ha, ih ys zs b hb]
          simp only [List.cons_append, List.append_assoc]

theorem parsingSound : Comparators.GorbowFormulaPrefixCode.ParsingSound := by
  intro n k
  induction k generalizing n with
  | zero => intro raw rest φ h; simp [parse] at h
  | succ k ih =>
      intro raw rest φ h
      cases raw with
      | nil => simp [parse] at h
      | cons tag xs =>
          by_cases ht : tag ≤ 11
          · interval_cases tag
            · exact binary_sound n 0 GorbowTermPrefixCode.encode (GorbowTermPrefixCode.parse n k) Formula.equal
                (fun _ _ => rfl) (GorbowTermPrefixCodeProof.parsingSound n k) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 1 GorbowTermPrefixCode.encode (GorbowTermPrefixCode.parse n k) Formula.universalRelation
                (fun _ => rfl) (GorbowTermPrefixCodeProof.parsingSound n k) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 2 GorbowTermPrefixCode.encode (GorbowTermPrefixCode.parse n k) Formula.agent
                (fun _ => rfl) (GorbowTermPrefixCodeProof.parsingSound n k) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 3 GorbowTermPrefixCode.encode (GorbowTermPrefixCode.parse n k) Formula.knowledgeAll
                (fun _ => rfl) (GorbowTermPrefixCodeProof.parsingSound n k) xs rest φ (by simpa only [parse] using h)
            · exact binary_sound n 4 GorbowTermPrefixCode.encode (GorbowTermPrefixCode.parse n k) Formula.knowledge
                (fun _ _ => rfl) (GorbowTermPrefixCodeProof.parsingSound n k) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 5 GorbowTermPrefixCode.encode (GorbowTermPrefixCode.parse n k) Formula.truth
                (fun _ => rfl) (GorbowTermPrefixCodeProof.parsingSound n k) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 6 encode (parse n k) Formula.neg
                (fun _ => rfl) (ih n) xs rest φ (by simpa only [parse] using h)
            · exact binary_sound n 7 encode (parse n k) Formula.imp
                (fun _ _ => rfl) (ih n) xs rest φ (by simpa only [parse] using h)
            · exact binary_sound n 8 encode (parse n k) Formula.conj
                (fun _ _ => rfl) (ih n) xs rest φ (by simpa only [parse] using h)
            · exact binary_sound n 9 encode (parse n k) Formula.disj
                (fun _ _ => rfl) (ih n) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 10 encode (parse (n + 1) k) Formula.all
                (fun _ => rfl) (ih (n + 1)) xs rest φ (by simpa only [parse] using h)
            · exact unary_sound n 11 encode (parse (n + 1) k) Formula.ex
                (fun _ => rfl) (ih (n + 1)) xs rest φ (by simpa only [parse] using h)
          · have hg : 12 ≤ tag := by omega
            obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hg
            have he : tag = m + 12 := by omega
            rw [he] at h
            simp [parse] at h

theorem parsingComplete : Comparators.GorbowFormulaPrefixCode.ParsingComplete := by
  intro n φ
  induction φ with
  | equal t u =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : GorbowTermPrefixCode.height t ≤ k := by simp only [height] at hk; omega
          have hku : GorbowTermPrefixCode.height u ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, GorbowTermPrefixCodeProof.parsingComplete _ t k hkt, GorbowTermPrefixCodeProof.parsingComplete _ u k hku, bind, Option.bind_some]
  | universalRelation t =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : GorbowTermPrefixCode.height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, GorbowTermPrefixCodeProof.parsingComplete _ t k hkt, bind, Option.bind_some]
  | agent t =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : GorbowTermPrefixCode.height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, GorbowTermPrefixCodeProof.parsingComplete _ t k hkt, bind, Option.bind_some]
  | knowledgeAll t =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : GorbowTermPrefixCode.height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, GorbowTermPrefixCodeProof.parsingComplete _ t k hkt, bind, Option.bind_some]
  | knowledge t u =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : GorbowTermPrefixCode.height t ≤ k := by simp only [height] at hk; omega
          have hku : GorbowTermPrefixCode.height u ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, GorbowTermPrefixCodeProof.parsingComplete _ t k hkt, GorbowTermPrefixCodeProof.parsingComplete _ u k hku, bind, Option.bind_some]
  | truth t =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : GorbowTermPrefixCode.height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, GorbowTermPrefixCodeProof.parsingComplete _ t k hkt, bind, Option.bind_some]
  | neg t ht =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ht k hkt, bind, Option.bind_some]
  | imp t u ht hu =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : height t ≤ k := by simp only [height] at hk; omega
          have hku : height u ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ht k hkt, hu k hku, bind, Option.bind_some]
  | conj t u ht hu =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : height t ≤ k := by simp only [height] at hk; omega
          have hku : height u ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ht k hkt, hu k hku, bind, Option.bind_some]
  | disj t u ht hu =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : height t ≤ k := by simp only [height] at hk; omega
          have hku : height u ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ht k hkt, hu k hku, bind, Option.bind_some]
  | all t ht =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ht k hkt, bind, Option.bind_some]
  | ex t ht =>
      intro k hk rest
      cases k with
      | zero => simp [height] at hk
      | succ k =>
          have hkt : height t ≤ k := by simp only [height] at hk; omega
          simp only [encode, List.cons_append, List.append_assoc, parse, ht k hkt, bind, Option.bind_some]

theorem finiteFuel : Comparators.GorbowFormulaPrefixCode.FiniteFuel := by
  intro n φ
  induction φ with
  | equal t u | knowledge t u =>
      have ht := GorbowTermPrefixCodeProof.finiteFuel _ t
      have hu := GorbowTermPrefixCodeProof.finiteFuel _ u
      simp only [height, encode, List.length_cons, List.length_append]
      omega
  | universalRelation t | agent t | knowledgeAll t | truth t =>
      have ht := GorbowTermPrefixCodeProof.finiteFuel _ t
      simp only [height, encode, List.length_cons]
      omega
  | neg φ h | all φ h | ex φ h =>
      simp only [height, encode, List.length_cons]
      omega
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
      simp only [height, encode, List.length_cons, List.length_append]
      omega

theorem decoderExact : Comparators.GorbowFormulaPrefixCode.DecoderExact := by
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

theorem encodingInjective : Comparators.GorbowFormulaPrefixCode.EncodingInjective := by
  intro d a b h
  have ha := (decoderExact d (encode a) a).mpr rfl
  have hb := (decoderExact d (encode b) b).mpr rfl
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem binderContext : Comparators.GorbowFormulaPrefixCode.BinderContext := by
  intro n k raw rest φ h
  simp [parse, h]

theorem gorbowFormulaPrefixCode : Comparators.GorbowFormulaPrefixCode.Target :=
  ⟨parsingSound, parsingComplete, finiteFuel, decoderExact, encodingInjective, binderContext⟩
end LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

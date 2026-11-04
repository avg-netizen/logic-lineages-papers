module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientTargets

@[expose] public section

/-! The frozen context codec uses Encodable.finPi for Boolean tables, whereas
the primitive-recursion library uses finArrow. They are different encodings.
This module proves the ORIGINAL decoder primitive, without changing its bytes.
Canonical finite decoding has finite support and hence is a literal finite
lookup program. No arbitrary finite-output decoder is assumed computable. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof

open Source OrdinaryArithmeticQuotient

def Canonical (α : Type) (e : Encodable α) : Prop :=
  ∀ k a, @Encodable.decode α e k = some a → @Encodable.encode α e a = k

theorem canonicalEquiv {α β : Type} (e : Encodable α) (h : Canonical α e) (f : β ≃ α) :
    Canonical β (@Encodable.ofEquiv β α e f) := by
  intro k b hb
  rw [Encodable.decode_ofEquiv] at hb
  obtain ⟨a, ha, hab⟩ := Option.map_eq_some_iff.mp hb
  have he : f b = a := by rw [← hab]; exact f.apply_symm_apply a
  change @Encodable.encode α e (f b) = k
  rw [he]
  exact h k a ha

theorem canonicalNat : Canonical Nat Nat.encodable := by
  intro k a h
  simpa using h.symm

theorem canonicalBool : Canonical Bool Bool.encodable := by
  intro k b h
  cases k with
  | zero =>
    have hb : b = false := by simpa using h.symm
    subst b
    rfl
  | succ k =>
    cases k with
    | zero =>
      have hb : b = true := by simpa using h.symm
      subst b
      rfl
    | succ k =>
      rw [Encodable.decode_ge_two (k + 2) (by omega)] at h
      contradiction

theorem canonicalSubtype {α : Type} (e : Encodable α) (h : Canonical α e)
    (p : α → Prop) [DecidablePred p] :
    Canonical (Subtype p) (@Subtype.encodable α p e inferInstance) := by
  intro k a ha
  change (@Encodable.decode α e k).bind (fun b =>
    if hb : p b then some ⟨b, hb⟩ else none) = some a at ha
  obtain ⟨b, hb, hba⟩ := Option.bind_eq_some_iff.mp ha
  split_ifs at hba with hp
  · have eq : b = a.val := congrArg Subtype.val (Option.some.inj hba)
    change @Encodable.encode α e a.val = k
    rw [← eq]
    exact h k b hb

theorem canonicalFin (n : Nat) : Canonical (Fin n) (Fin.encodable n) :=
  canonicalEquiv _ (canonicalSubtype _ canonicalNat (fun k => k < n)) Fin.equivSubtype

theorem canonicalList {α : Type} (e : Encodable α) (h : Canonical α e) :
    Canonical (List α) (@List.encodable α e) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro l hl
    cases k with
    | zero =>
      have he : l = [] := by simpa only [Encodable.decode_list_zero, Option.some.injEq] using hl.symm
      subst l
      rfl
    | succ k =>
      rw [Encodable.decode_list_succ] at hl
      cases hx : @Encodable.decode α e k.unpair.1 with
      | none =>
        simp only [hx] at hl
        change none = some l at hl
        contradiction
      | some x =>
        cases hy : @Encodable.decode (List α) (@List.encodable α e) k.unpair.2 with
        | none =>
          simp only [hx, hy] at hl
          change none = some l at hl
          contradiction
        | some ys =>
          have he : l = x :: ys := by simpa [hx, hy] using hl.symm
          subst l
          rw [Encodable.encode_list_cons, h _ _ hx,
            ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le k)) _ hy, Nat.pair_unpair]

theorem canonicalSigma {α : Type} {β : α → Type} (e : Encodable α)
    (d : ∀ a, Encodable (β a)) (h : Canonical α e) (hd : ∀ a, Canonical (β a) (d a)) :
    Canonical (Sigma β) (@Sigma.encodable α β e d) := by
  intro k a ha
  rw [Encodable.decode_sigma_val] at ha
  obtain ⟨b, hb, hba⟩ := Option.bind_eq_some_iff.mp ha
  obtain ⟨c, hc, hca⟩ := Option.map_eq_some_iff.mp hba
  subst a
  change Nat.pair (@Encodable.encode α e b) (@Encodable.encode (β b) (d b) c) = k
  rw [h _ _ hb, hd b _ _ hc, Nat.pair_unpair]

theorem canonicalFinArrow {α : Type} (e : Encodable α) (h : Canonical α e) (n : Nat) :
    Canonical (Fin n → α) (@Encodable.finArrow α e n) := by
  apply canonicalEquiv
  exact canonicalSubtype _ (canonicalList e h) (fun l : List α => l.length = n)

theorem canonicalFinPi (n : Nat) {β : Fin n → Type} (d : ∀ i, Encodable (β i))
    (hd : ∀ i, Canonical (β i) (d i)) :
    Canonical (∀ i, β i) (@Encodable.finPi n β d) := by
  apply canonicalEquiv
  apply canonicalSubtype
  exact canonicalFinArrow _ (canonicalSigma _ d (canonicalFin n) hd) n

theorem tableCanonical (n : Nat) :
    Canonical (Fin n → Fin n → Bool) (inferInstance : Encodable (Fin n → Fin n → Bool)) :=
  canonicalFinPi n _ (fun _ => canonicalFinPi n _ (fun _ => canonicalBool))

/-- This finite-support argument applies ONLY to a proved canonical decoder.
The arbitrary values of a noncanonical decoder are never smuggled into PR. -/
theorem finiteCanonicalDecoder {α : Type} [Fintype α] [Primcodable α]
    (e : Encodable α) (h : Canonical α e) : Primrec (@Encodable.decode α e) := by
  classical
  let bound := Finset.univ.sup (@Encodable.encode α e)
  let l : List (Option α) := List.ofFn (fun i : Fin (bound + 1) =>
    @Encodable.decode α e (i : Nat))
  have hp : Primrec (fun k : Nat => (l[k]?).getD none) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.const l) Primrec.id)
      (Primrec.const none)
  apply hp.of_eq
  intro k
  by_cases hk : k < bound + 1
  · have hl : k < l.length := by simpa [l] using hk
    rw [List.getElem?_eq_getElem hl, Option.getD_some]
    simp only [l, List.getElem_ofFn]
  · have hl : l.length ≤ k := by simp [l]; omega
    rw [List.getElem?_eq_none_iff.mpr hl, Option.getD_none]
    symm
    cases hd : @Encodable.decode α e k with
    | none => rfl
    | some a =>
      have he := h k a hd
      have hb : @Encodable.encode α e a ≤ bound := Finset.le_sup (Finset.mem_univ a)
      omega

theorem tableDecoderPrimitive (n : Nat) :
    Primrec (Encodable.decode : Nat → Option (Fin n → Fin n → Bool)) :=
  finiteCanonicalDecoder _ (tableCanonical n)

theorem contextDecoderPrimitive (n : Nat) :
    Primrec (Encodable.decode : Nat → Option (Context n)) := by
  have windowP : Primrec (Encodable.decode : Nat → Option (List (Fin n) × List Ty)) := by
    apply (Primrec.decode (α := List (Fin n) × List Ty)).of_eq
    intro k
    with_reducible_and_instances rfl
  have hleft := windowP.comp (Primrec.fst.comp Primrec.unpair)
  have hright := (tableDecoderPrimitive n).comp (Primrec.snd.comp Primrec.unpair)
  have hbody : Primrec (fun p : (Nat × (List (Fin n) × List Ty)) ×
      (Fin n → Fin n → Bool) => (p.1.2, p.2)) :=
    (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  have hmap : Primrec (fun p : Nat × (List (Fin n) × List Ty) =>
      (Encodable.decode (α := Fin n → Fin n → Bool) p.1.unpair.2).map
        (fun table => (p.2, table))) :=
    Primrec.option_map (hright.comp Primrec.fst) hbody.to₂
  apply (Primrec.option_bind hleft hmap.to₂).of_eq
  intro k
  simp only [Encodable.decode_prod_val]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof

module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodeOperations
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodecProof
public import LogicLineages.ComputabilityKnowledge.ExponentialHereditaryCodecProof

@[expose] public section

/-! Explicit primitive-recursive construction of the code operations.
This is a Codex-authored continuation. It uses the complete hereditary-code
supplier as a proved theorem, rather than assuming a canonicalization oracle.
It must be compiled only after that supplier's full frozen gate passes.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsEffectivity

open ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormCodeOperations ExponentialNormalFormCodecProof

private theorem pr_canonicalize :
    Primrec (fun p : Nat × Nat × Nat => canonicalize p.1 p.2.1 p.2.2) :=
  ExponentialHereditaryCodecProof.hereditaryCodec.2.2.2.2.2.1

private theorem pr_zeroCode : Primrec (fun p : Nat × Nat => zeroCode p.1 p.2) :=
  ExponentialHereditaryCodecProof.hereditaryCodec.2.2.2.2.2.2.1

theorem pr_parseCoefficients : Primrec parseCoefficients :=
  Primrec.option_getD.comp (Primrec.decode (α := CoeffCode)) (Primrec.const [])

theorem pr_parseEntries : Primrec parseEntries :=
  Primrec.option_getD.comp (Primrec.decode (α := MapCode)) (Primrec.const [])

theorem pr_canonicalEntries :
    Primrec (fun p : Nat × Nat × Nat => canonicalEntries p.1 p.2.1 p.2.2) :=
  pr_parseEntries.comp pr_canonicalize

private theorem pr_singleCode {α : Type} [Primcodable α]
    {d key : α → Nat} {coeff : α → CoeffCode}
    (hd : Primrec d) (hk : Primrec key) (hc : Primrec coeff) :
    Primrec (fun x => Encodable.encode (normalizeMap (d x) [(key x, coeff x)])) :=
  Primrec.encode.comp (pr_normalizeMap.comp
    (hd.pair (Primrec.list_cons.comp (hk.pair hc) (Primrec.const []))))

theorem pr_variableCode :
    Primrec (fun p : Nat × Nat × Nat => variableCode p.1 p.2.1 p.2.2) := by
  let d : Nat × Nat × Nat → Nat := fun p => p.1
  let h : Nat × Nat × Nat → Nat := fun p => p.2.1
  let i : Nat × Nat × Nat → Nat := fun p => p.2.2
  have hd : Primrec d := Primrec.fst
  have hh : Primrec h := Primrec.fst.comp Primrec.snd
  have hi : Primrec i := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p => coeffVariable (d p) (i p)) :=
    pr_variable.comp (hd.pair hi)
  have hz : Primrec (fun p => zeroCode (d p) (h p - 1)) :=
    pr_zeroCode.comp (hd.pair (Primrec.nat_sub.comp hh (Primrec.const 1)))
  have raw := Primrec.ite (Primrec.eq.comp hh (Primrec.const 0))
    (Primrec.encode.comp hc) (pr_singleCode hd hz hc)
  apply raw.of_eq
  rintro ⟨d, h, i⟩
  cases h <;> rfl

theorem pr_addCode :
    Primrec (fun p : Nat × Nat × Nat × Nat => addCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let d : Nat × Nat × Nat × Nat → Nat := fun p => p.1
  let h : Nat × Nat × Nat × Nat → Nat := fun p => p.2.1
  let a : Nat × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let b : Nat × Nat × Nat × Nat → Nat := fun p => p.2.2.2
  have hd : Primrec d := Primrec.fst
  have hh : Primrec h := Primrec.fst.comp Primrec.snd
  have ha : Primrec a := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec b := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbase : Primrec (fun p => Encodable.encode
      (coeffAdd (d p) (parseCoefficients (a p)) (parseCoefficients (b p)))) :=
    Primrec.encode.comp (pr_add.comp (hd.pair
      ((pr_parseCoefficients.comp ha).pair (pr_parseCoefficients.comp hb))))
  have hea : Primrec (fun p => canonicalEntries (d p) (h p) (a p)) :=
    pr_canonicalEntries.comp (hd.pair (hh.pair ha))
  have heb : Primrec (fun p => canonicalEntries (d p) (h p) (b p)) :=
    pr_canonicalEntries.comp (hd.pair (hh.pair hb))
  have hsucc := Primrec.encode.comp (pr_normalizeMap.comp
    (hd.pair (Primrec.list_append.comp hea heb)))
  apply (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) hbase hsucc).of_eq
  rintro ⟨d, h, a, b⟩
  cases h <;> rfl

theorem pr_constantCoefficientCode :
    Primrec (fun p : Nat × Nat × Nat => constantCoefficientCode p.1 p.2.1 p.2.2) := by
  let d : Nat × Nat × Nat → Nat := fun p => p.1
  let h : Nat × Nat × Nat → Nat := fun p => p.2.1
  let n : Nat × Nat × Nat → Nat := fun p => p.2.2
  have hd : Primrec d := Primrec.fst
  have hh : Primrec h := Primrec.fst.comp Primrec.snd
  have hn : Primrec n := Primrec.snd.comp Primrec.snd
  have he : Primrec (fun p => canonicalEntries (d p) (h p) (n p)) :=
    pr_canonicalEntries.comp (hd.pair (hh.pair hn))
  have hz : Primrec (fun p => zeroCode (d p) (h p - 1)) :=
    pr_zeroCode.comp (hd.pair (Primrec.nat_sub.comp hh (Primrec.const 1)))
  have hstep : Primrec₂ (fun (p : Nat × Nat × Nat) (q : (Nat × CoeffCode) × Nat) =>
      if q.1.1 = zeroCode (d p) (h p - 1) then q.1.2.getD 0 0 + q.2 else q.2) := by
    have hk : Primrec (fun x : (Nat × Nat × Nat) × ((Nat × CoeffCode) × Nat) => x.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hc : Primrec (fun x : (Nat × Nat × Nat) × ((Nat × CoeffCode) × Nat) => x.2.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hacc : Primrec (fun x : (Nat × Nat × Nat) × ((Nat × CoeffCode) × Nat) => x.2.2) :=
      Primrec.snd.comp Primrec.snd
    exact (Primrec.ite (Primrec.eq.comp hk (hz.comp Primrec.fst))
      (Primrec.nat_add.comp ((Primrec.list_getD 0).comp hc (Primrec.const 0)) hacc)
      hacc).to₂
  have hsucc := Primrec.list_foldr he (Primrec.const 0) hstep
  have hbase := (Primrec.list_getD 0).comp (pr_parseCoefficients.comp hn) (Primrec.const 0)
  apply (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) hbase hsucc).of_eq
  rintro ⟨d, h, n⟩
  cases h <;> rfl

theorem pr_removeCode :
    Primrec (fun p : Nat × Nat × Nat => removeCode p.1 p.2.1 p.2.2) := by
  let d : Nat × Nat × Nat → Nat := fun p => p.1
  let h : Nat × Nat × Nat → Nat := fun p => p.2.1
  let n : Nat × Nat × Nat → Nat := fun p => p.2.2
  have hd : Primrec d := Primrec.fst
  have hh : Primrec h := Primrec.fst.comp Primrec.snd
  have hn : Primrec n := Primrec.snd.comp Primrec.snd
  have he : Primrec (fun p => canonicalEntries (d p) (h p) (n p)) :=
    pr_canonicalEntries.comp (hd.pair (hh.pair hn))
  have hz : Primrec (fun p => zeroCode (d p) (h p - 1)) :=
    pr_zeroCode.comp (hd.pair (Primrec.nat_sub.comp hh (Primrec.const 1)))
  have hstep : Primrec₂ (fun (p : Nat × Nat × Nat) (e : Nat × CoeffCode) =>
      (e.1, if e.1 = zeroCode (d p) (h p - 1) then coeffRemove (d p) e.2 else e.2)) := by
    have hk : Primrec (fun x : (Nat × Nat × Nat) × (Nat × CoeffCode) => x.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hc : Primrec (fun x : (Nat × Nat × Nat) × (Nat × CoeffCode) => x.2.2) :=
      Primrec.snd.comp Primrec.snd
    exact (hk.pair (Primrec.ite (Primrec.eq.comp hk (hz.comp Primrec.fst))
      (pr_remove.comp ((hd.comp Primrec.fst).pair hc)) hc)).to₂
  have hsucc := Primrec.encode.comp (pr_normalizeMap.comp
    (hd.pair (Primrec.list_map he hstep)))
  have hbase := Primrec.encode.comp
    (pr_remove.comp (hd.pair (pr_parseCoefficients.comp hn)))
  apply (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) hbase hsucc).of_eq
  rintro ⟨d, h, n⟩
  cases h <;> rfl

private def rekey (es : MapCode) (rs : List Nat) : MapCode :=
  (List.range es.length).map (fun i => (rs.getD i 0, (es.getD i (0, [])).2))

private theorem pr_rekey : Primrec (fun p : MapCode × List Nat => rekey p.1 p.2) := by
  unfold rekey
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
  exact (((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd).pair
    (Primrec.snd.comp ((Primrec.list_getD (0, ([] : CoeffCode))).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd))).to₂

private theorem rekey_map (es : MapCode) (F : Nat × CoeffCode → Nat) :
    rekey es (es.map F) = es.map (fun e => (F e, e.2)) := by
  apply List.ext_getElem
  · simp [rekey]
  · intro i hleft hright
    have hi : i < es.length := by simpa using hright
    simp [rekey, hi]

theorem pr_raiseCode :
    Primrec (fun p : Nat × Nat × Nat => raiseCode p.1 p.2.1 p.2.2) := by
  let f : Nat × Nat × Nat → Nat := fun p => raiseCode p.1 p.2.1 p.2.2
  let children : Nat × Nat × Nat → List (Nat × Nat × Nat) := fun p =>
    if p.2.1 = 0 then [] else
      (canonicalEntries p.1 p.2.1 p.2.2).map (fun e => (p.1, p.2.1 - 1, e.1))
  let assemble : Nat × Nat × Nat → List Nat → Option Nat := fun p rs =>
    some (if p.2.1 = 0 then
      Encodable.encode (normalizeMap p.1
        [(zeroCode p.1 0, coeffNormalize p.1 (parseCoefficients p.2.2))])
    else Encodable.encode (normalizeMap p.1
      (rekey (canonicalEntries p.1 p.2.1 p.2.2) rs)))
  have hd : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hh : Primrec (fun p : Nat × Nat × Nat => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Nat × Nat × Nat => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hchildren : Primrec children := by
    apply Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) (Primrec.const [])
    apply Primrec.list_map pr_canonicalEntries
    exact ((hd.comp Primrec.fst).pair
      ((Primrec.nat_sub.comp (hh.comp Primrec.fst) (Primrec.const 1)).pair
        (Primrec.fst.comp Primrec.snd))).to₂
  have hbase : Primrec (fun p : Nat × Nat × Nat =>
      Encodable.encode (normalizeMap p.1
        [(zeroCode p.1 0, coeffNormalize p.1 (parseCoefficients p.2.2))])) :=
    pr_singleCode hd (pr_zeroCode.comp (hd.pair (Primrec.const 0)))
      (pr_normalize.comp (hd.pair (pr_parseCoefficients.comp hn)))
  have hassemble : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite ((Primrec.eq.comp hh (Primrec.const 0)).comp Primrec.fst)
      (hbase.comp Primrec.fst)
    exact Primrec.encode.comp (pr_normalizeMap.comp
      ((hd.comp Primrec.fst).pair
        (pr_rekey.comp ((pr_canonicalEntries.comp Primrec.fst).pair Primrec.snd))))
  apply Primrec.nat_omega_rec' f hh hchildren hassemble
  · intro p q hq
    by_cases h0 : p.2.1 = 0
    · simp [children, h0] at hq
    · have hMap : q ∈ (canonicalEntries p.1 p.2.1 p.2.2).map
          (fun e => (p.1, p.2.1 - 1, e.1)) := by
        simpa only [children, if_neg h0] using hq
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hMap
      dsimp
      omega
  · rintro ⟨d, h, n⟩
    cases h with
    | zero => rfl
    | succ h =>
        simp [children, assemble, f, raiseCode, List.map_map, rekey_map]

theorem actualPrimitiveRecursion :
    Comparators.ExponentialNormalFormCodeOperations.ActualPrimitiveRecursion :=
  ⟨pr_variableCode, pr_addCode, pr_constantCoefficientCode, pr_removeCode, pr_raiseCode⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsEffectivity

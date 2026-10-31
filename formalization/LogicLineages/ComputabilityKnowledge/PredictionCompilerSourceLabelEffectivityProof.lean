module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivityTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivity
open Turing.PartrecToTM2 PredictionCompilerFinitePayloadCodec PredictionCompilerSourceLabelExplicitCodec

theorem decodePrimitiveRecursive : Targets.DecodePrimitiveRecursive :=
  Primrec.encode_iff.mp normalizationPrimitiveRecursive

theorem structuralFoldPrimitiveRecursive : Targets.StructuralFoldPrimitiveRecursive := by
  intro α inst z step hs
  exact ((foldPrimitiveRecursive α z step hs).comp (show Primrec code from Primrec.encode)).of_eq
    (fun q => foldCorrect α z step q)

theorem finiteTablePrimitiveRecursive : Targets.FiniteTablePrimitiveRecursive := by
  intro α inst
  exact ⟨Primrec.of_equiv, Primrec.of_equiv_symm, Primrec.of_equiv, Primrec.of_equiv_symm⟩

private theorem pr_node {β : Type} [Primcodable β] {t p a b c d e : β → Nat}
    (ht : Primrec t) (hp : Primrec p) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (he : Primrec e) : Primrec (fun x => node (t x) (p x) (a x,b x,c x,d x,e x)) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp hp (Primrec₂.natPair.comp ha (Primrec₂.natPair.comp hb
      (Primrec₂.natPair.comp hc (Primrec₂.natPair.comp hd he)))))) ht) (Primrec.const 1)

private theorem decode_node (tag p : Nat) (cs : Quint Label) (ht : tag < 8) :
    decode (node tag p (code cs.1, code cs.2.1, code cs.2.2.1, code cs.2.2.2.1, code cs.2.2.2.2)) =
      assemble tag p cs := by
  let ns := (code cs.1, code cs.2.1, code cs.2.2.1, code cs.2.2.2.1, code cs.2.2.2.2)
  have hn : node tag p ns ≠ 0 := by unfold node; omega
  have hm : (node tag p ns - 1) % 8 = tag := by unfold node; omega
  have hd : (node tag p ns - 1) / 8 = Nat.pair p (pack ns) := by unfold node; omega
  change fold (.ret .halt) assemble (node tag p ns) = assemble tag p cs
  rw [fold]
  simp only [hn, ↓reduceDIte, hm, hd, pack, ns, Nat.unpair_pair]
  change assemble tag p (decode (code cs.1), decode (code cs.2.1), decode (code cs.2.2.1),
    decode (code cs.2.2.2.1), decode (code cs.2.2.2.2)) = assemble tag p cs
  rw [roundtrip cs.1, roundtrip cs.2.1, roundtrip cs.2.2.1, roundtrip cs.2.2.2.1, roundtrip cs.2.2.2.2]

private theorem assemble_min (t p : Nat) (cs : Quint Label) : assemble (min t 7) p cs = assemble t p cs := by
  by_cases h : t ≤ 7
  · rw [Nat.min_eq_left h]
  · have h7 : 7 ≤ t := by omega
    rw [Nat.min_eq_right h7]
    have h0 : t ≠ 0 := by omega
    have h1 : t ≠ 1 := by omega
    have h2 : t ≠ 2 := by omega
    have h3 : t ≠ 3 := by omega
    have h4 : t ≠ 4 := by omega
    have h5 : t ≠ 5 := by omega
    have h6 : t ≠ 6 := by omega
    simp [assemble, h0, h1, h2, h3, h4, h5, h6]

theorem assemblyPrimitiveRecursive : Targets.AssemblyPrimitiveRecursive := by
  have he : Primrec code := Primrec.encode
  have ht : Primrec (fun x : Nat × Nat × Quint Label => min x.1 7) :=
    Primrec.nat_min.comp Primrec.fst (Primrec.const 7)
  have hp : Primrec (fun x : Nat × Nat × Quint Label => x.2.1) := Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun x : Nat × Nat × Quint Label => x.2.2) := Primrec.snd.comp Primrec.snd
  have ha := he.comp (Primrec.fst.comp hg)
  have hb := he.comp (Primrec.fst.comp (Primrec.snd.comp hg))
  have hc := he.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hg)))
  have hd := he.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hg))))
  have hi := he.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hg))))
  apply (decodePrimitiveRecursive.comp (pr_node ht hp ha hb hc hd hi)).of_eq
  intro x
  rw [decode_node _ _ _ (by omega), assemble_min]

theorem inspectPrimitiveRecursive : Targets.InspectPrimitiveRecursive := by
  have he : Primrec code := Primrec.encode
  have ht : Primrec (fun q : Label => (code q - 1) % 8) :=
    Primrec.nat_mod.comp (Primrec.pred.comp he) (Primrec.const 8)
  have hd : Primrec (fun q : Label => (code q - 1) / 8) :=
    Primrec.nat_div.comp (Primrec.pred.comp he) (Primrec.const 8)
  have hp := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hright {β : Type} [Primcodable β] {f : β → Nat} (h : Primrec f) : Primrec (fun x => (f x).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp h)
  have hleft {β : Type} [Primcodable β] {f : β → Nat} (h : Primrec f) : Primrec (fun x => (f x).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp h)
  have ha := decodePrimitiveRecursive.comp (hleft hr)
  have hb := decodePrimitiveRecursive.comp (hleft (hright hr))
  have hc := decodePrimitiveRecursive.comp (hleft (hright (hright hr)))
  have hd' := decodePrimitiveRecursive.comp (hleft (hright (hright (hright hr))))
  have hi := decodePrimitiveRecursive.comp (hright (hright (hright (hright hr))))
  apply (ht.pair (hp.pair (ha.pair (hb.pair (hc.pair (hd'.pair hi)))))).of_eq
  intro q
  have hm (t p : Nat) (cs : Quint Nat) (ht : t < 8) : (node t p cs - 1) % 8 = t := by unfold node; omega
  have hv (t p : Nat) (cs : Quint Nat) (ht : t < 8) : (node t p cs - 1) / 8 = Nat.pair p (pack cs) := by unfold node; omega
  have hround (q : Label) : decode (code q) = q := roundtrip q
  have hz : decode 0 = Λ'.ret Cont'.halt := by unfold decode; rw [fold]; simp
  cases q <;> simp [code, inspect, hm, hv, pack, hround, hz]
end LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivity

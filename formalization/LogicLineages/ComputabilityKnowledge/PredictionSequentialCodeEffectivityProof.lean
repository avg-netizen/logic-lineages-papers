module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivityTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivity
open PredictionSequentialCodeCodec

theorem constructorPrimitiveRecursive : Targets.ConstructorPrimitiveRecursive := by
  have he : Primrec code := Primrec.encode
  have hbin (k : Nat) : Primrec (fun p : Code × Code => 8 * Nat.pair (code p.1) (code p.2) + k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (he.comp Primrec.fst) (he.comp Primrec.snd))) (Primrec.const k)
  refine ⟨Primrec.encode_iff.mp (hbin 3), Primrec.encode_iff.mp (hbin 4),
    Primrec.encode_iff.mp (hbin 5), ?_⟩
  apply Primrec.encode_iff.mp
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp he (Primrec.const 0))) (Primrec.const 6)

theorem decodePrimitiveRecursive : Targets.DecodePrimitiveRecursive :=
  Primrec.encode_iff.mp normalizationPrimitiveRecursive

theorem structuralFoldPrimitiveRecursive : Targets.StructuralFoldPrimitiveRecursive := by
  intro α inst leaf branch hl hb
  exact ((foldPrimitiveRecursive α leaf branch hl hb).comp (show Primrec code from Primrec.encode)).of_eq
    (fun c => foldCorrect α leaf branch c)

theorem casesPrimitiveRecursive : Targets.CasesPrimitiveRecursive := by
  intro α inst leaf branch hl hb
  have he : Primrec code := Primrec.encode
  have hm : Primrec (fun c : Code => code c % 8) := Primrec.nat_mod.comp he (Primrec.const 8)
  have hd : Primrec (fun c : Code => code c / 8) := Primrec.nat_div.comp he (Primrec.const 8)
  have hleft := decodePrimitiveRecursive.comp (Primrec.fst.comp (Primrec.unpair.comp hd))
  have hright := decodePrimitiveRecursive.comp (Primrec.snd.comp (Primrec.unpair.comp hd))
  have h : Primrec (fun c : Code => if code c % 8 < 3 then leaf (code c % 8)
      else branch (code c % 8) (decode (code c / 8).unpair.1) (decode (code c / 8).unpair.2)) :=
    Primrec.ite (Primrec.nat_lt.comp hm (Primrec.const 3)) (hl.comp hm)
      (hb.comp (hm.pair (hleft.pair hright)))
  apply h.of_eq
  intro c
  have hmod (p t : Nat) (ht : t < 8) : (8 * p + t) % 8 = t := by omega
  have hdiv (p t : Nat) (ht : t < 8) : (8 * p + t) / 8 = p := by omega
  have hz : decode 0 = Turing.ToPartrec.Code.zero' := roundtrip .zero'
  have hround (c : Code) : decode (code c) = c := roundtrip c
  cases c <;> simp [code, cases, hmod, hdiv, hround, hz]
end LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeEffectivity

module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivityTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivity
open PredictionSequentialContinuationCodec
open PredictionSequentialCodeCodec (Code)

theorem listPrimitiveRecursive : Targets.ListPrimitiveRecursive :=
  ⟨Primrec.of_equiv, Primrec.of_equiv_symm⟩

theorem constructorPrimitiveRecursive : Targets.ConstructorPrimitiveRecursive := by
  have hl : Primrec toList := listPrimitiveRecursive.1
  have hcons₁ : Primrec (fun p : Code × Cont => some (Sum.inl p.1 : Code ⊕ (Code ⊕ Code)) :: toList p.2) :=
    Primrec.list_cons.comp (Primrec.option_some.comp (Primrec.sumInl.comp Primrec.fst)) (hl.comp Primrec.snd)
  have hcons₂ : Primrec (fun k : Cont => (none : Frame) :: toList k) :=
    Primrec.list_cons.comp (Primrec.const none) hl
  have hcomp : Primrec (fun p : Code × Cont => some (Sum.inr (Sum.inl p.1) : Code ⊕ (Code ⊕ Code)) :: toList p.2) :=
    Primrec.list_cons.comp (Primrec.option_some.comp (Primrec.sumInr.comp (Primrec.sumInl.comp Primrec.fst))) (hl.comp Primrec.snd)
  have hfix : Primrec (fun p : Code × Cont => some (Sum.inr (Sum.inr p.1) : Code ⊕ (Code ⊕ Code)) :: toList p.2) :=
    Primrec.list_cons.comp (Primrec.option_some.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.fst))) (hl.comp Primrec.snd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Primrec (fun p : Code × Cont => Turing.PartrecToTM2.Cont'.cons₁ p.1 p.2)
    apply Primrec.encode_iff.mp
    change Primrec (fun p : Code × Cont => Encodable.encode (some (Sum.inl p.1 : Code ⊕ (Code ⊕ Code)) :: toList p.2))
    exact Primrec.encode.comp hcons₁
  · apply Primrec.encode_iff.mp
    change Primrec (fun k : Cont => Encodable.encode ((none : Frame) :: toList k))
    exact Primrec.encode.comp hcons₂
  · change Primrec (fun p : Code × Cont => Turing.PartrecToTM2.Cont'.comp p.1 p.2)
    apply Primrec.encode_iff.mp
    change Primrec (fun p : Code × Cont => Encodable.encode (some (Sum.inr (Sum.inl p.1) : Code ⊕ (Code ⊕ Code)) :: toList p.2))
    exact Primrec.encode.comp hcomp
  · change Primrec (fun p : Code × Cont => Turing.PartrecToTM2.Cont'.fix p.1 p.2)
    apply Primrec.encode_iff.mp
    change Primrec (fun p : Code × Cont => Encodable.encode (some (Sum.inr (Sum.inr p.1) : Code ⊕ (Code ⊕ Code)) :: toList p.2))
    exact Primrec.encode.comp hfix

theorem decodePrimitiveRecursive : Targets.DecodePrimitiveRecursive :=
  listPrimitiveRecursive.2.comp
    (Primrec.option_getD.comp (Primrec.decode (α := List Frame)) (Primrec.const []))

theorem casesPrimitiveRecursive : Targets.CasesPrimitiveRecursive := by
  intro α inst z step hs
  have hl : Primrec toList := listPrimitiveRecursive.1
  have hr : Primrec fromList := listPrimitiveRecursive.2
  have h : Primrec (fun k : Cont => List.casesOn (motive := fun _ => α) (toList k) z (fun x xs => step x (fromList xs))) :=
    Primrec.list_casesOn hl (Primrec.const z)
      (hs.comp (Primrec.fst.comp Primrec.snd) (hr.comp (Primrec.snd.comp Primrec.snd))).to₂
  apply h.of_eq
  intro k
  have hround (k : Cont) : fromList (toList k) = k := listRoundtrip.1 k
  cases k <;> simp [toList, cases, hround]
end LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivity

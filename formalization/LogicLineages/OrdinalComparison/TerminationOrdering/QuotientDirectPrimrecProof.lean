module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecProof
open Source QuotientDirectPrimrec QuotientDirectPrimrecSupportProof QuotientDirectCertificates

theorem dominationPrimitive : QuotientDirectPrimrecTargets.ActualDominationPrimitive := by
  intro n arity Gamma
  have hf : Primrec (fun p : Parameters n × List Nat × List Nat × List QuotientDominationCertificates.Entry =>
      p.2.2.2.foldl (step n arity Gamma (p.1,p.2.1)) (p.2.2.1,true)) :=
    Primrec.list_foldl (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))) ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))).pair (Primrec.const true))
      ((stepPrimitive n arity Gamma).comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.id)).pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id)))).pair (Primrec.snd.comp Primrec.id))).to₂
  have hend : Primrec finish :=
    Primrec.and.comp (Primrec.eq.comp Primrec.fst (Primrec.const [])).decide Primrec.snd
  exact (hend.comp hf).of_eq (by intro p; simpa using foldCalibration n arity Gamma (p.1,p.2.1) p.2.2.1 p.2.2.2 true)

theorem directPrimitive : QuotientDirectPrimrecTargets.ActualDirectPrimitive := by
  intro n arity Gamma
  have hk : Primrec (fun p : Parameters n × List Nat × List Nat × Certificate => p.2.2.2.1.1) := (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))
  have hr : Primrec (fun p : Parameters n × List Nat × List Nat × Certificate => p.2.2.2.1.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))
  have hi : Primrec (fun p : Parameters n × List Nat × List Nat × Certificate => p.2.2.2.1.2.2) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))
  have he : Primrec (fun p : Parameters n × List Nat × List Nat × Certificate => p.2.2.2.2) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  have hp := NumberedExchangeGuardsPrimrecProof.permutationPrimitive Nat
  have hs := hp.comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.id)).pair (Primrec.list_append.comp hk hr))
  have ht := hp.comp ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))).pair (Primrec.list_append.comp hk hi))
  have hn := (Primrec.eq.comp hr (Primrec.const [])).not.decide
  have hd := (dominationPrimitive n arity Gamma).comp (Primrec.fst.pair (hr.pair (hi.pair he)))
  exact (Primrec.and.comp (Primrec.and.comp hs (Primrec.and.comp ht hn)) hd).of_eq (by
    intro p; simp only [directTest,Bool.decide_and]; rfl)

theorem numericDirectPrimitive : QuotientDirectPrimrecTargets.ActualNumericDirectPrimitive := by
  intro n arity Gamma
  let Input := Parameters n × Nat × Nat × Nat
  have hc : Primrec (fun p : (Input × List Nat) × List Nat =>
      (Encodable.decode (α := Certificate) p.1.1.2.2.2).any (fun c =>
        directTest n arity p.1.1.1.1.1 p.1.1.1.1.2 Gamma p.1.1.1.2 p.1.2 p.2 c)) :=
    optionAnyPrimitive (Primrec.decode.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))))
      ((directPrimitive n arity Gamma).comp ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id)))).pair ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))).pair ((Primrec.snd.comp (Primrec.fst.comp Primrec.id)).pair (Primrec.snd.comp Primrec.id))))).to₂
  have ht : Primrec (fun p : Input × List Nat =>
      (Encodable.decode (α := List Nat) p.1.2.2.1).any (fun ts =>
        (Encodable.decode (α := Certificate) p.1.2.2.2).any (fun c =>
          directTest n arity p.1.1.1.1 p.1.1.1.2 Gamma p.1.1.2 p.2 ts c))) :=
    optionAnyPrimitive (Primrec.decode.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))) hc.to₂
  exact optionAnyPrimitive (Primrec.decode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))) ht.to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecProof

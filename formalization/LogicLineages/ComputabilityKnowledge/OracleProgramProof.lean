module

public import LogicLineages.ComputabilityKnowledge.OracleProgramTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleProgramProof
open OracleProgram OracleProgramTargets

theorem injectiveProgramEncoding : InjectiveProgramEncoding := by
  intro p
  induction p with
  | base c =>
      intro q h
      cases q <;> simp_all [encode, tagged, Nat.pair_eq_pair, Encodable.encode_inj]
  | query =>
      intro q h
      cases q <;> simp_all [encode, tagged, Nat.pair_eq_pair]
  | pair p q ihp ihq =>
      intro r h
      cases r <;> simp only [encode, tagged, Nat.add_left_inj, Nat.pair_eq_pair] at h <;>
        try { simp at h }
      exact congrArg₂ Program.pair (ihp h.2.1) (ihq h.2.2)
  | comp p q ihp ihq =>
      intro r h
      cases r <;> simp only [encode, tagged, Nat.add_left_inj, Nat.pair_eq_pair] at h <;>
        try { simp at h }
      exact congrArg₂ Program.comp (ihp h.2.1) (ihq h.2.2)
  | prec p q ihp ihq =>
      intro r h
      cases r <;> simp only [encode, tagged, Nat.add_left_inj, Nat.pair_eq_pair] at h <;>
        try { simp at h }
      exact congrArg₂ Program.prec (ihp h.2.1) (ihq h.2.2)
  | mu p ih =>
      intro q h
      cases q <;> simp only [encode, tagged, Nat.add_left_inj, Nat.pair_eq_pair] at h <;>
        try { simp at h }
      exact congrArg Program.mu (ih h.2)

theorem oracleEvaluationSound : OracleEvaluationSound := by
  intro g p
  induction p with
  | base c =>
      exact RecursiveIn.iff_nat.mp ((Nat.Partrec.Code.eval_part.comp
        (Computable.const c) Computable.id).recursiveIn)
  | query => exact Nat.RecursiveIn.oracle g rfl
  | pair p q ihp ihq => exact ihp.pair ihq
  | comp p q ihp ihq => exact ihp.comp ihq
  | prec p q ihp ihq => exact ihp.prec ihq
  | mu p ih => exact ih.rfind

theorem oracleEvaluationComplete : OracleEvaluationComplete := by
  intro g f hf
  induction hf with
  | zero => exact ⟨.base .zero, rfl⟩
  | succ => exact ⟨.base .succ, rfl⟩
  | left => exact ⟨.base .left, rfl⟩
  | right => exact ⟨.base .right, rfl⟩
  | oracle h hh =>
      have heq : h = g := hh
      subst h
      exact ⟨.query, rfl⟩
  | pair hf hh ihf ihh =>
      obtain ⟨p, rfl⟩ := ihf
      obtain ⟨q, rfl⟩ := ihh
      exact ⟨.pair p q, rfl⟩
  | comp hf hh ihf ihh =>
      obtain ⟨p, rfl⟩ := ihf
      obtain ⟨q, rfl⟩ := ihh
      exact ⟨.comp p q, rfl⟩
  | prec hf hh ihf ihh =>
      obtain ⟨p, rfl⟩ := ihf
      obtain ⟨q, rfl⟩ := ihh
      exact ⟨.prec p q, rfl⟩
  | rfind hf ih =>
      obtain ⟨p, rfl⟩ := ih
      exact ⟨.mu p, rfl⟩

theorem ordinaryBaseCalibration : OrdinaryBaseCalibration := by
  intro g c n
  rfl

theorem oracleSpecializationSemantics : OracleSpecializationSemantics := by
  intro g p a x
  simp [specialize, eval, Nat.Partrec.Code.eval_const, Nat.Partrec.Code.eval_id, Seq.seq]

private theorem pr_tagged : Primrec₂ tagged :=
  Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem uniformEncodedSpecialization : UniformEncodedSpecialization := by
  refine ⟨?_, fun p a => rfl⟩
  have hconst : Primrec (fun z : Nat × Nat => tagged 0 (Encodable.encode (Nat.Partrec.Code.const z.2))) :=
    pr_tagged.comp (Primrec.const 0)
      (Primrec.encode.comp (Nat.Partrec.Code.primrec_const.comp Primrec.snd))
  have hpair := pr_tagged.comp (Primrec.const 2)
    (Primrec₂.natPair.comp hconst (Primrec.const (tagged 0 (Encodable.encode Nat.Partrec.Code.id))))
  exact pr_tagged.comp (Primrec.const 3) (Primrec₂.natPair.comp Primrec.fst hpair)

end LogicLineages.ComputabilityKnowledge.OracleProgramProof

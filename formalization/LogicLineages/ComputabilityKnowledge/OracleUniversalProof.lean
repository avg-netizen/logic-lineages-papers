module

public import LogicLineages.ComputabilityKnowledge.OracleUniversalTargets
public import LogicLineages.ComputabilityKnowledge.OracleCertificateProof
public import LogicLineages.ComputabilityKnowledge.OracleDerivationProof
public import LogicLineages.ComputabilityKnowledge.OracleDecoderProof
public import LogicLineages.ComputabilityKnowledge.OracleProgramProof
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleUniversalProof
open OracleProgram OracleDecoder OracleDerivation OracleCertificate OracleRelativeRecursion
open OracleUniversal OracleUniversalTargets

private theorem pr_nodeData : Primrec nodeData :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
private theorem pr_nodeCode : Primrec nodeCode := Primrec.fst.comp (Primrec.unpair.comp pr_nodeData)
private theorem pr_nodeInput : Primrec nodeInput :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData)))
private theorem pr_nodeOutput : Primrec nodeOutput :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData)))))

private def rawTest (z : Nat) : Nat :=
  if z.unpair.1 = 1 ∧ nodeCode z.unpair.2.unpair.2 = z.unpair.2.unpair.1.unpair.1 ∧
      nodeInput z.unpair.2.unpair.2 = z.unpair.2.unpair.1.unpair.2 then 0 else 1

private theorem pr_rawTest : Primrec rawTest := by
  have hf : Primrec (fun z : Nat => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hc : Primrec (fun z : Nat => z.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hq : Primrec (fun z : Nat => z.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact Primrec.ite ((Primrec.eq.comp hf (Primrec.const 1)).and
    ((Primrec.eq.comp (pr_nodeCode.comp hc) (Primrec.fst.comp (Primrec.unpair.comp hq))).and
      (Primrec.eq.comp (pr_nodeInput.comp hc) (Primrec.snd.comp (Primrec.unpair.comp hq)))))
    (Primrec.const 0) (Primrec.const 1)

theorem relativeCertificateTest : RelativeCertificateTest := by
  intro g
  let O : Set (Nat → Part Nat) := {fun n => Part.some (g n)}
  have hflag := OracleRelativeRecursionProof.relativeComposition O _ _
    (OracleCertificateProof.relativeCertificateVerifier g) (Primrec.snd.comp Primrec.unpair).computableIn
  have hp := OracleRelativeRecursionProof.relativeNumericPairing O _ _ hflag Primrec.id.computableIn
  have h := OracleRelativeRecursionProof.relativeComposition O _ _ pr_rawTest.computableIn hp
  apply h.of_eq
  intro z
  simp only [rawTest, Nat.unpair_pair, certificateFlag, certificateTest]
  cases validCertificate g z.unpair.2 <;> simp [Bool.and_eq_true, and_assoc]

theorem relativeUniversalEvaluation : RelativeUniversalEvaluation := by
  intro g
  have hs := OracleRelativeRecursionProof.relativePartialSearch _ _ (relativeCertificateTest g)
  apply RecursiveIn.iff_nat.mpr
  apply ((RecursiveIn.iff_nat.mp pr_nodeOutput.computableIn).comp (RecursiveIn.iff_nat.mp hs)).of_eq
  intro q
  exact Part.bind_some_eq_map _ _

private theorem test_iff (g : Nat → Nat) (query i : Nat) :
    certificateTest g (Nat.pair query i) = 0 ↔
      validCertificate g i = true ∧ nodeCode i = query.unpair.1 ∧ nodeInput i = query.unpair.2 := by
  simp [certificateTest, Bool.and_eq_true, and_assoc]

private theorem search_spec (g : Nat → Nat) (query i : Nat)
    (hi : i ∈ zeroSearch (certificateTest g) query) :
    validCertificate g i = true ∧ nodeCode i = query.unpair.1 ∧ nodeInput i = query.unpair.2 := by
  apply (test_iff g query i).mp
  have h := Nat.rfind_spec hi
  exact of_decide_eq_true (Part.mem_some_iff.mp h).symm

private theorem search_exists (g : Nat → Nat) (query i : Nat)
    (hi : certificateTest g (Nat.pair query i) = 0) :
    ∃ j, j ∈ zeroSearch (certificateTest g) query := by
  apply Part.dom_iff_mem.mp
  apply Nat.rfind_dom.mpr
  exact ⟨i, by simp [hi], fun {_} _ => trivial⟩

private theorem universal_iff (g : Nat → Nat) (query output : Nat) :
    output ∈ universal g query ↔ ∃ p, encode p = query.unpair.1 ∧
      output ∈ eval (fun n => Part.some (g n)) p query.unpair.2 := by
  constructor
  · intro ho
    obtain ⟨i, hi, hout⟩ := (Part.mem_map_iff _).mp ho
    have hm := search_spec g query i hi
    obtain ⟨p, hp, hd⟩ := OracleCertificateProof.numericCertificateSound g i hm.1
    refine ⟨p, hp.trans hm.2.1, ?_⟩
    have hv := OracleDerivationProof.finiteDerivationSound g p _ _ hd
    simpa only [hm.2.2, hout] using hv
  · rintro ⟨p, hp, ho⟩
    have hd := OracleDerivationProof.finiteDerivationComplete g p _ _ ho
    obtain ⟨i, hv, hc, hin, hout⟩ := OracleCertificateProof.numericCertificateComplete g p _ _ hd
    have ht : certificateTest g (Nat.pair query i) = 0 :=
      (test_iff g query i).mpr ⟨hv, hc.trans hp, hin⟩
    obtain ⟨j, hj⟩ := search_exists g query i ht
    have hm := search_spec g query j hj
    obtain ⟨q, hq, hder⟩ := OracleCertificateProof.numericCertificateSound g j hm.1
    have heq : q = p := OracleProgramProof.injectiveProgramEncoding
      ((hq.trans hm.2.1).trans hp.symm)
    subst q
    have hvalue := OracleDerivationProof.finiteDerivationSound g p _ _ hder
    rw [hm.2.2] at hvalue
    exact (Part.mem_map_iff _).mpr ⟨j, hj, Part.mem_unique hvalue ho⟩

theorem encodedUniversalSemantics : EncodedUniversalSemantics := by
  intro g p input output
  rw [universal_iff]
  simp only [Nat.unpair_pair]
  constructor
  · rintro ⟨q, hq, h⟩
    have heq := OracleProgramProof.injectiveProgramEncoding hq
    simpa only [heq] using h
  · exact fun h => ⟨p, rfl, h⟩

theorem malformedUniversalDivergence : MalformedUniversalDivergence := by
  intro g index input hi
  apply Part.eq_none_iff.mpr
  intro output ho
  obtain ⟨p, hp, _⟩ := (universal_iff g _ output).mp ho
  simp only [Nat.unpair_pair] at hp
  have hd := OracleDecoderProof.oracleDecoderComplete p
  rw [hp, hi] at hd
  contradiction

theorem decodedUniversalCalibration : DecodedUniversalCalibration := by
  intro g query
  cases hd : decode query.unpair.1 with
  | none =>
      have h := malformedUniversalDivergence g query.unpair.1 query.unpair.2 hd
      simpa only [Nat.pair_unpair, decodedEvaluation, hd] using h
  | some p =>
      have he := OracleDecoderProof.oracleDecoderSound _ _ hd
      apply Part.ext
      intro output
      have h := encodedUniversalSemantics g p query.unpair.2 output
      rw [he, Nat.pair_unpair] at h
      simpa only [decodedEvaluation, hd] using h

end LogicLineages.ComputabilityKnowledge.OracleUniversalProof

module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorCode
public import LogicLineages.ComputabilityKnowledge.WWOrdinalPrefixCodeProof
public import LogicLineages.ComputabilityKnowledge.WWBoundedVectorPaddingProof
public import LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof

@[expose] public section

/-! Actual uniform original-vector code construction after independent target
freeze and faithful O-codec acceptance. Hardness remains a separate supplier. -/
namespace LogicLineages.ComputabilityKnowledge.WWBoundedVectorCodeProof

open PositiveExpression CircuitReduction FiniteComparisonEnumeration
open WWBoundedVectorPadding WWBoundedVectorCode ExponentialNormalizerProgram

private theorem encode_embed (d : Nat) (e : Expr (Fin d)) :
    WWOrdinalPrefixCode.encode (WWOrdinalTermSemantics.embed e) = encodeExpr (e.rename Fin.val) :=
  WWOrdinalPrefixCodeProof.embedCompatibility d e

private theorem depth_code (d : Nat) (e : Expr (Fin d)) :
    depthCode d (encodeExpr (e.rename Fin.val)) = some e.depth :=
  ExponentialNormalizerProgramSemantics.exactDepth d e

private theorem remainder_code (d : Nat) (u v : Expr (Fin d)) :
    remainderCode (encodeExpr (u.rename Fin.val)) (encodeExpr (v.rename Fin.val)) =
      encodeExpr ((remainder u v).rename Fin.val) := rfl

private theorem assemble_source (d : Nat) (u v : Expr (Fin d)) :
    assemble (encodeExpr (u.rename Fin.val)) (encodeExpr (v.rename Fin.val))
      (encodeExpr ((control u v).rename Fin.val)) = sourceOutput u v := by
  simp only [assemble, sourceOutput, left, weakRight, strictRight, List.map_cons, List.map_nil,
    head, WWOrdinalPrefixCode.encode, encode_embed,
    remainder_code, Expr.rename, encodeExpr]

theorem literalConstruction : Comparators.WWBoundedVectorCode.LiteralConstruction := by
  intro d u v hu hv
  have hg := WWFiniteEnvelopeProof.actualEncodedConstruction.2.1 d (remainder u v)
  simp only [paddingCode, depth_code, bind, Option.bind_some,
    withinDepth, hu, hv, decide_true, Bool.and_self, ↓reduceIte, remainder_code, hg]
  exact congrArg some (assemble_source d u v)

theorem exactRawDomain : Comparators.WWBoundedVectorCode.ExactRawDomain := by
  intro d a b
  constructor
  · intro h
    have hda : (depthCode d a).isSome = true := by
      cases ha : depthCode d a with
      | none => simp [paddingCode, ha] at h
      | some da => rfl
    have hdb : (depthCode d b).isSome = true := by
      cases ha : depthCode d a with
      | none => simp [paddingCode, ha] at h
      | some da =>
          cases hb : depthCode d b with
          | none => simp [paddingCode, ha, hb] at h
          | some db => rfl
    have hpa : (decodeExpr d a).isSome = true := by
      rw [← (ExponentialNormalizerProgramSemantics.rawDomain d 0 a).2]
      exact hda
    have hpb : (decodeExpr d b).isSome = true := by
      rw [← (ExponentialNormalizerProgramSemantics.rawDomain d 0 b).2]
      exact hdb
    obtain ⟨u, rfl⟩ := (ExponentialIdentityProof.rawInputCoverage d a).mp hpa
    obtain ⟨v, rfl⟩ := (ExponentialIdentityProof.rawInputCoverage d b).mp hpb
    by_cases hu : u.depth ≤ 2
    · by_cases hv : v.depth ≤ 2
      · exact ⟨u, v, rfl, rfl, hu, hv⟩
      · simp [paddingCode, depth_code, withinDepth, hu, hv] at h
    · simp [paddingCode, depth_code, withinDepth, hu] at h
  · rintro ⟨u, v, rfl, rfl, hu, hv⟩
    rw [literalConstruction d u v hu hv]
    rfl

private theorem pr_remainderCode : Primrec (fun p : List Nat × List Nat => remainderCode p.1 p.2) := by
  have hab := Primrec.list_append.comp (Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_append.comp Primrec.fst Primrec.snd)) (Primrec.const [0])
  exact Primrec.list_cons.comp (Primrec.const 2) hab

private theorem pr_assemble : Primrec (fun p : List Nat × List Nat × List Nat => assemble p.1 p.2.1 p.2.2) := by
  have ha : Primrec (fun p : List Nat × List Nat × List Nat => p.1) := Primrec.fst
  have hb : Primrec (fun p : List Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun p : List Nat × List Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hr := pr_remainderCode.comp (ha.pair hb)
  have hh := Primrec.list_cons.comp (Primrec.const 6) (Primrec.list_append.comp hr hg)
  have hv1 := Primrec.list_cons.comp (Primrec.const 2) (Primrec.list_append.comp hb (Primrec.const [0]))
  have hh1 := Primrec.list_cons.comp (Primrec.const 2) (Primrec.list_append.comp hh (Primrec.const [0]))
  have hl := Primrec.list_cons.comp hh (Primrec.list_cons.comp hv1 (Primrec.const []))
  have hw := Primrec.list_cons.comp hh (Primrec.list_cons.comp ha (Primrec.const []))
  have hs := Primrec.list_cons.comp hh1 (Primrec.list_cons.comp ha (Primrec.const []))
  exact (hl.pair (hw.pair hs)).of_eq (fun _ => rfl)

private theorem pr_withinDepth : Primrec (fun p : Nat × Nat => withinDepth p.1 p.2) :=
  Primrec.and.comp (Primrec.nat_le.comp Primrec.fst (Primrec.const 2)).decide
    (Primrec.nat_le.comp Primrec.snd (Primrec.const 2)).decide

abbrev Input := Nat × List Nat × List Nat

private theorem comp_build : Computable (fun p : Input =>
    (FiniteDepthEnvelope.envelopeCode p.1 (remainderCode p.2.1 p.2.2)).map (assemble p.2.1 p.2.2)) := by
  have hr : Computable (fun p : Input => remainderCode p.2.1 p.2.2) :=
    pr_remainderCode.to_comp.comp Computable.snd
  have hg := WWFiniteEnvelopeProof.actualEncodedConstruction.1.comp (Computable.fst.pair hr)
  have hargs : Computable (fun q : Input × List Nat => (q.1.2.1, q.1.2.2, q.2)) :=
    (Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
  exact Computable.option_map hg ((pr_assemble.to_comp.comp hargs).of_eq (fun _ => rfl)).to₂

private theorem comp_guard : Computable (fun q : (Input × Nat) × Nat =>
    if withinDepth q.1.2 q.2 then
      (FiniteDepthEnvelope.envelopeCode q.1.1.1 (remainderCode q.1.1.2.1 q.1.1.2.2)).map
        (assemble q.1.1.2.1 q.1.1.2.2)
    else none) := by
  have hargs : Computable (fun q : (Input × Nat) × Nat => (q.1.2, q.2)) :=
    (Computable.snd.comp Computable.fst).pair Computable.snd
  have hc : Computable (fun q : (Input × Nat) × Nat => withinDepth q.1.2 q.2) :=
    (pr_withinDepth.to_comp.comp hargs).of_eq (fun _ => rfl)
  have hbase : Computable (fun q : (Input × Nat) × Nat => q.1.1) :=
    Computable.fst.comp Computable.fst
  have hb := comp_build.comp hbase
  exact (Computable.cond hc hb (Computable.const none)).of_eq (by
    intro q
    cases withinDepth q.1.2 q.2 <;> rfl)

private theorem pr_depthA : Primrec (fun p : Input => depthCode p.1 p.2.1) := by
  have hargs : Primrec (fun p : Input => (p.1, p.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  exact (ExponentialNormalizerProgramEffectivity.pr_depthCode.comp hargs).of_eq (fun _ => rfl)

private theorem pr_depthB : Primrec (fun p : Input => depthCode p.1 p.2.2) := by
  have hargs : Primrec (fun p : Input => (p.1, p.2.2)) :=
    Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  exact (ExponentialNormalizerProgramEffectivity.pr_depthCode.comp hargs).of_eq (fun _ => rfl)

private theorem comp_inner : Computable (fun q : Input × Nat => do
    let db ← depthCode q.1.1 q.1.2.2
    if withinDepth q.2 db then
      (FiniteDepthEnvelope.envelopeCode q.1.1 (remainderCode q.1.2.1 q.1.2.2)).map
        (assemble q.1.2.1 q.1.2.2)
    else none) := by
  have hb : Computable (fun q : Input × Nat => depthCode q.1.1 q.1.2.2) :=
    pr_depthB.to_comp.comp Computable.fst
  exact Computable.option_bind hb comp_guard.to₂

theorem actualUniformProgram : Comparators.WWBoundedVectorCode.ActualUniformProgram := by
  have ha : Computable (fun p : Input => depthCode p.1 p.2.1) :=
    pr_depthA.to_comp
  exact (Computable.option_bind ha comp_inner.to₂).of_eq (by
    intro p
    cases hda : depthCode p.1 p.2.1 <;>
      cases hdb : depthCode p.1 p.2.2 <;>
      cases hg : FiniteDepthEnvelope.envelopeCode p.1 (remainderCode p.2.1 p.2.2) <;>
      simp [paddingCode, hda, hdb, hg])

theorem certifiedSourceReduction : Comparators.WWBoundedVectorCode.CertifiedSourceReduction := by
  intro d u v hu hv
  obtain ⟨hL, hW, hS, nL, nW, nS⟩ := WWBoundedVectorPaddingProof.originalBoundedVectors d u v hu hv
  have hc := WWBoundedVectorPaddingProof.exactComparisonReduction d u v hu hv
  exact ⟨⟨sourceOutput u v, literalConstruction d u v hu hv, rfl⟩,
    hL, hW, hS, nL, nW, nS, hc.1, hc.2⟩

theorem wwBoundedVectorCode : Comparators.WWBoundedVectorCode.Target :=
  ⟨exactRawDomain, literalConstruction, actualUniformProgram, certifiedSourceReduction⟩

end LogicLineages.ComputabilityKnowledge.WWBoundedVectorCodeProof

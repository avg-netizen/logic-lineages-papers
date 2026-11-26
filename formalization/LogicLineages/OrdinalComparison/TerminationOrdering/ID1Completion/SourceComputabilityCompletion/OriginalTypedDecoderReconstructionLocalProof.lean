module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderExpansionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding OriginalTypedDecoder
open OriginalTypedDecoderCodecProof OriginalTypedDecoderExpansionProof

theorem contextNumber (Gamma : List Ty) : Encodable.encode Gamma = typesNumber Gamma := by
  induction Gamma with
  | nil => rfl
  | cons tau Gamma ih =>
    rw [OriginalContextExtensionCalibrationProof.contextEncoding, typesNumber, ih]
    omega

theorem typesEncodingSurjective : Function.Surjective typesNumber := by
  intro value
  obtain ⟨Gamma, hGamma⟩ := contextEncodingSurjective value
  exact ⟨Gamma, (contextNumber Gamma).symm.trans hGamma⟩

theorem headReconstruct (n : Nat) (arity : Fin n → Nat) (raw : Nat)
    (h : headSignatureValue n arity raw ≠ 0) :
    ∃ head : HeadCode (Fin n), headNumber head = raw := by
  cases hd : decodeHeadNumber n raw with
  | none => simp [headSignatureValue, hd] at h
  | some head =>
    refine ⟨head, ?_⟩
    simp only [decodeHeadNumber, Option.filter_eq_some_iff, decide_eq_true_eq] at hd
    exact hd.2

/-- Only the original constructor tags can lead to a successful expansion. -/
theorem expansionShape (H : Nat → Nat) (request : Nat) (children : List Nat)
    (h : expandValue H request = some children) :
    (requestMode request = 0 ∧ (Nat.unpair (requestRaw request)).1 < 6) ∨
    (requestMode request = 1 ∧
      ((Nat.unpair (requestRaw request)).1 = 6 ∨ (Nat.unpair (requestRaw request)).1 = 7)) := by
  by_cases hm : requestMode request = 0
  · refine Or.inl ⟨hm, ?_⟩
    by_contra hn
    have h0 : (Nat.unpair (requestRaw request)).1 ≠ 0 := by omega
    have h1 : (Nat.unpair (requestRaw request)).1 ≠ 1 := by omega
    have h2 : (Nat.unpair (requestRaw request)).1 ≠ 2 := by omega
    have h3 : (Nat.unpair (requestRaw request)).1 ≠ 3 := by omega
    have h4 : (Nat.unpair (requestRaw request)).1 ≠ 4 := by omega
    have h5 : (Nat.unpair (requestRaw request)).1 ≠ 5 := by omega
    simp [expandValue,hm,h0,h1,h2,h3,h4,h5] at h
  · by_cases ha : requestMode request = 1
    · refine Or.inr ⟨ha, ?_⟩
      by_contra hn
      have h6 : (Nat.unpair (requestRaw request)).1 ≠ 6 := fun hh => hn (Or.inl hh)
      have h7 : (Nat.unpair (requestRaw request)).1 ≠ 7 := fun hh => hn (Or.inr hh)
      simp [expandValue,hm,ha,h6,h7] at h
    · simp [expandValue,hm,ha] at h

/-- Backward local reconstruction uses only original numeric constructor
codes. Contexts, requested types and dependent typing are not assumed. -/
theorem expansionReconstruct (n : Nat) (arity : Fin n → Nat) (request : Nat)
    (children : List Nat)
    (h : expandValue (headSignatureValue n arity) request = some children)
    (hc : ∀ child ∈ children, ∃ code : Code (Fin n), codeNumber code = requestRaw child) :
    ∃ code : Code (Fin n), codeNumber code = requestRaw request := by
  let g := requestGamma request
  let t := requestType request
  let p := (Nat.unpair (requestRaw request)).2
  have hp : Nat.pair (Nat.unpair (requestRaw request)).1 p = requestRaw request :=
    Nat.pair_unpair _
  rcases expansionShape _ request children h with ⟨hm, htag⟩ | ⟨hm, htag⟩
  · have tags : (Nat.unpair (requestRaw request)).1 = 0 ∨
        (Nat.unpair (requestRaw request)).1 = 1 ∨
        (Nat.unpair (requestRaw request)).1 = 2 ∨
        (Nat.unpair (requestRaw request)).1 = 3 ∨
        (Nat.unpair (requestRaw request)).1 = 4 ∨
        (Nat.unpair (requestRaw request)).1 = 5 := by omega
    rcases tags with ht | ht | ht | ht | ht | ht
    · refine ⟨.var p, ?_⟩
      simpa only [codeNumber, ht] using hp
    · have hx : (t ≠ 0 ∧ (Nat.unpair (t - 1)).1 = (Nat.unpair p).1) ∧
          [termRequestValue (1 + Nat.pair (Nat.unpair p).1 g)
            (Nat.unpair (t - 1)).2 (Nat.unpair p).2] = children := by
        simpa [expandValue, hm, ht, Option.ite_none_right_eq_some, g, t, p] using h
      obtain ⟨body, hb⟩ := hc (termRequestValue (1 + Nat.pair (Nat.unpair p).1 g)
        (Nat.unpair (t - 1)).2 (Nat.unpair p).2) (by rw [← hx.2]; simp)
      obtain ⟨sigma, hs⟩ := NumberedTypeCodecTotalProof.typeCodeBijection.2 (Nat.unpair p).1
      refine ⟨.lam sigma body, ?_⟩
      simpa only [codeNumber, termRaw, hs, hb, Nat.pair_unpair, ht] using hp
    · have hx : [termRequestValue g (1 + Nat.pair (Nat.unpair p).1 t)
          (Nat.unpair (Nat.unpair p).2).1,
          termRequestValue g (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).2] = children := by
        simpa [expandValue, hm, ht, g, t, p] using h
      obtain ⟨q, hq⟩ := hc (termRequestValue g (1 + Nat.pair (Nat.unpair p).1 t)
        (Nat.unpair (Nat.unpair p).2).1) (by rw [← hx]; simp)
      obtain ⟨a, ha⟩ := hc (termRequestValue g (Nat.unpair p).1
        (Nat.unpair (Nat.unpair p).2).2) (by rw [← hx]; simp)
      obtain ⟨sigma, hs⟩ := NumberedTypeCodecTotalProof.typeCodeBijection.2 (Nat.unpair p).1
      refine ⟨.app sigma q a, ?_⟩
      simpa only [codeNumber, hq, ha, termRaw, hs, Nat.pair_unpair, ht] using hp
    · obtain ⟨tau, htau⟩ := NumberedTypeCodecTotalProof.typeCodeBijection.2 p
      refine ⟨.bottom tau, ?_⟩
      simpa only [codeNumber, htau, ht] using hp
    · let sig := headSignatureValue n arity (Nat.unpair p).1
      have hx : (sig ≠ 0 ∧ (Nat.unpair (sig - 1)).1 = t) ∧
          [argumentsRequestValue g (Nat.unpair (sig - 1)).2 (Nat.unpair p).2] = children := by
        simpa [expandValue, hm, ht, Option.ite_none_right_eq_some, sig, g, t, p] using h
      obtain ⟨head, hh⟩ := headReconstruct n arity (Nat.unpair p).1 hx.1.1
      obtain ⟨base, hb⟩ := hc (argumentsRequestValue g (Nat.unpair (sig - 1)).2
        (Nat.unpair p).2) (by rw [← hx.2]; simp)
      refine ⟨.ordinary head base, ?_⟩
      simpa only [codeNumber, hb, argumentsRaw, hh, Nat.pair_unpair, ht] using hp
    · let p1 := (Nat.unpair p).2
      let p2 := (Nat.unpair p1).2
      let p3 := (Nat.unpair p2).2
      let p4 := (Nat.unpair p3).2
      let sig := headSignatureValue n arity (Nat.unpair p1).1
      have hx : (sig ≠ 0 ∧ (Nat.unpair p2).1 = t) ∧
          [argumentsRequestValue g (Nat.unpair (sig - 1)).2 (Nat.unpair p3).1,
            argumentsRequestValue g (Nat.unpair p4).1 (Nat.unpair p4).2] = children := by
        simpa [expandValue, hm, ht, Option.ite_none_right_eq_some,
          sig, g, t, p4, p3, p2, p1, p] using h
      obtain ⟨head, hh⟩ := headReconstruct n arity (Nat.unpair p1).1 hx.1.1
      obtain ⟨base, hb⟩ := hc (argumentsRequestValue g
        (Nat.unpair (sig - 1)).2 (Nat.unpair p3).1) (by rw [← hx.2]; simp)
      obtain ⟨extras, he⟩ := hc (argumentsRequestValue g
        (Nat.unpair p4).1 (Nat.unpair p4).2) (by rw [← hx.2]; simp)
      obtain ⟨tau, htau⟩ := NumberedTypeCodecTotalProof.typeCodeBijection.2 (Nat.unpair p2).1
      obtain ⟨types, htypes⟩ := typesEncodingSurjective (Nat.unpair p4).1
      refine ⟨.numbered (Nat.unpair p).1 head tau base types extras, ?_⟩
      simp only [codeNumber, hh, htau, hb, he, argumentsRaw, htypes]
      simpa only [p4, p3, p2, p1, Nat.pair_unpair, ht] using hp
  · rcases htag with ht | ht
    · have hx : (p = 0 ∧ t = 0) ∧ [] = children := by
        simpa [expandValue, hm, ht, Option.ite_none_right_eq_some, g, t, p] using h
      refine ⟨.argumentsNil, ?_⟩
      simpa only [codeNumber, ht, hx.1.1] using hp
    · have hx : (t ≠ 0 ∧ (Nat.unpair (t - 1)).1 = (Nat.unpair p).1) ∧
          [termRequestValue g (Nat.unpair p).1 (Nat.unpair (Nat.unpair p).2).1,
            argumentsRequestValue g (Nat.unpair (t - 1)).2
              (Nat.unpair (Nat.unpair p).2).2] = children := by
        simpa [expandValue, hm, ht, Option.ite_none_right_eq_some, g, t, p] using h
      obtain ⟨q, hq⟩ := hc (termRequestValue g (Nat.unpair p).1
        (Nat.unpair (Nat.unpair p).2).1) (by rw [← hx.2]; simp)
      obtain ⟨rest, hr⟩ := hc (argumentsRequestValue g (Nat.unpair (t - 1)).2
        (Nat.unpair (Nat.unpair p).2).2) (by rw [← hx.2]; simp)
      obtain ⟨tau, htau⟩ := NumberedTypeCodecTotalProof.typeCodeBijection.2 (Nat.unpair p).1
      refine ⟨.argumentsCons tau q rest, ?_⟩
      simpa only [codeNumber, hq, hr, termRaw, argumentsRaw, htau, Nat.pair_unpair, ht] using hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof

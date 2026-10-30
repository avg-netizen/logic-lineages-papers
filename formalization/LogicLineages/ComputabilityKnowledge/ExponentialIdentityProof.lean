module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialIdentity
public import LogicLineages.ComputabilityKnowledge.RaySeparationProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProof
public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof

@[expose] public section

/-! External N4 proof after independent exact target freeze. Completeness is
obtained from the proved original-form ray separation. Literal parser coverage
and height coherence are proved explicitly rather than assumed. -/
namespace LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof

open PositiveExpression ExponentialNormalForm ExponentialHereditaryCodec
open ExponentialNormalizer ExponentialNormalizerProgram CircuitReduction
open FiniteComparisonEnumeration RayFamilyClosure RayCoefficientCollection RayUniformBounds RayHeightInduction
open ExponentialIdentity

theorem originalFormCompleteness : Comparators.ExponentialIdentity.OriginalFormCompleteness := by
  intro d h f g hf hg
  constructor
  · intro heq
    obtain ⟨n, hn, hnf⟩ := ExponentialHereditaryCodecProof.coverage d h f
    obtain ⟨m, hm, hmg⟩ := ExponentialHereditaryCodecProof.coverage d h g
    have hc : ∀ k ∈ [n, m], CodeCanonical d h k := by
      intro k hk
      simp at hk
      rcases hk with rfl | rfl <;> assumption
    have hw : ∀ k ∈ [n, m], WellFormed h (formDecode d h k) := by
      intro k hk
      simp at hk
      rcases hk with rfl | rfl
      · simpa [hnf] using hf
      · simpa [hmg] using hg
    let T := commonThreshold d h [n, m]
    have hp := RayCoefficientCollectionProof.commonPositiveRay d h [n, m]
    have hcut : sharedCutoff h [n, m] ≤ T := le_max_left _ _
    let ρ : Fin d → PosNat := fun i => ⟨sharedRay d h [n, m] T i, (hp.2.2 i).2 T hcut⟩
    have hv := heq ρ
    have hs := RayHeightInductionProof.stableEqualityAndOrder d h [n, m] hc hw
      n (by simp) m (by simp) T le_rfl
    have hv' : rayValue d h [n, m] h (formDecode d h n) T =
        rayValue d h [n, m] h (formDecode d h m) T := by simpa [rayValue, hnf, hmg, ρ] using hv
    exact hnf.symm.trans ((hs.1.mp hv').trans hmg)
  · rintro rfl ρ
    rfl

theorem sourceN4 : Comparators.ExponentialIdentity.SourceN4 := by
  intro d a b
  have ha := ExponentialNormalizerProof.boundedNormalization d a (max a.depth b.depth) (le_max_left _ _)
  have hb := ExponentialNormalizerProof.boundedNormalization d b (max a.depth b.depth) (le_max_right _ _)
  rw [← originalFormCompleteness d _ _ _ ha.1 hb.1]
  constructor <;> intro h ρ
  · rw [ha.2 ρ, hb.2 ρ]
    exact h ρ
  · rw [← ha.2 ρ, ← hb.2 ρ]
    exact h ρ

private theorem bounded_finite (d : Nat) (e : Expr Nat) (he : Bounded d e) :
    ∃ f : Expr (Fin d), f.rename Fin.val = e := by
  induction e with
  | one => exact ⟨.one, rfl⟩
  | var i => exact ⟨.var ⟨i, he⟩, rfl⟩
  | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha he.1
      obtain ⟨b', rfl⟩ := hb he.2
      exact ⟨.add a' b', rfl⟩
  | emul a b ha hb =>
      obtain ⟨a', rfl⟩ := ha he.1
      obtain ⟨b', rfl⟩ := hb he.2
      exact ⟨.emul a' b', rfl⟩

theorem rawInputCoverage : Comparators.ExponentialIdentity.RawInputCoverage := by
  intro d raw
  constructor
  · intro h
    cases hd : decodeExpr d raw with
    | none => simp [hd] at h
    | some e =>
        have he := (FiniteComparisonEnumerationProof.expressionDecoderExact d raw e).mp hd
        obtain ⟨f, hf⟩ := bounded_finite d e he.2
        exact ⟨f, he.1.trans (congrArg encodeExpr hf.symm)⟩
  · rintro ⟨e, rfl⟩
    have hd := (FiniteComparisonEnumerationProof.expressionDecoderExact d _ (e.rename Fin.val)).mpr
      ⟨rfl, ExponentialNormalizerProgramSemantics.finite_rename_bounded d e⟩
    simp [hd]

theorem liftedNormalization : Comparators.ExponentialIdentity.LiftedNormalization := by
  intro d e H hH
  obtain ⟨n, hn, hc, hw, hv⟩ := ExponentialNormalizerProgramSemantics.fullEffectiveNormalization d e
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hH
  have ht := RayFamilyClosureProof.iteratedHeightTransport d e.depth extra n
  have hl := (RayFamilyClosureProof.originalEmbeddingLaws d e.depth extra).2 (formDecode d e.depth n)
  have hb := ExponentialNormalizerProof.boundedNormalization d e (e.depth + extra) (by omega)
  refine ⟨n, hn, ?_, ?_⟩
  · simpa only [liftCode, Nat.add_sub_cancel_left] using ht.1
  · simp only [liftCode, Nat.add_sub_cancel_left, ht.2]
    apply (originalFormCompleteness d _ _ _ (hl.2.2 hw) hb.1).mp
    intro ρ
    rw [hl.1, hv, hb.2]

private theorem normalize_domain (d : Nat) (raw : List Nat) :
    (normalizeCode d raw).isSome = (decodeExpr d raw).isSome := by
  have hd := (ExponentialNormalizerProgramSemantics.rawDomain d 0 raw).2
  cases he : depthCode d raw with
  | none => simp [normalizeCode, he] at hd ⊢; exact hd
  | some h =>
      have hh := (ExponentialNormalizerProgramSemantics.rawDomain d h raw).1
      cases hn : compileAt d h raw with
      | none => simp [normalizeCode, he, hn] at hh ⊢; exact hh
      | some n => simp [normalizeCode, he, hn] at hh ⊢; exact hh

theorem exactRawDomain : Comparators.ExponentialIdentity.ExactRawDomain := by
  intro d a b
  constructor
  · rw [← normalize_domain d a, ← normalize_domain d b]
    cases ha : normalizeCode d a <;> cases hb : normalizeCode d b <;>
      simp [decisionCode, normalInputs, ha, hb]
  · cases hp : normalInputs d a b with
    | none => simp [separatorCode, decisionCode, hp]
    | some pq => cases hs : sameCode d pq <;> simp [separatorCode, decisionCode, hp, hs]

theorem sourceDecision : Comparators.ExponentialIdentity.SourceDecision := by
  intro d a b
  let H := max a.depth b.depth
  obtain ⟨n, hn, hcn, hfn⟩ := liftedNormalization d a H (le_max_left _ _)
  obtain ⟨m, hm, hcm, hfm⟩ := liftedNormalization d b H (le_max_right _ _)
  have hmap : formDecode d H (liftCode d H (a.depth, n)) =
      formDecode d H (liftCode d H (b.depth, m)) ↔ ExtensionalEq a b := by
    rw [hfn, hfm]
    exact (sourceN4 d a b).symm
  have hcode : liftCode d H (a.depth, n) = liftCode d H (b.depth, m) ↔ ExtensionalEq a b :=
    (ExponentialHereditaryCodecProof.faithfulness d H _ _ hcn hcm).symm.trans hmap
  have hdec : decisionCode d (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some (decide (liftCode d H (a.depth, n) = liftCode d H (b.depth, m))) := by
    simp [decisionCode, normalInputs, hn, hm, sameCode, H]
  rw [hdec]
  constructor
  · simpa only [Option.some.injEq, decide_eq_true_eq] using hcode
  · simpa only [Option.some.injEq, decide_eq_false_iff_not] using not_congr hcode

private theorem map_mul_getD (xs : List Nat) (t i : Nat) :
    (xs.map (fun a => a * t)).getD i 0 = xs.getD i 0 * t := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem computedPositiveSeparator : Comparators.ExponentialIdentity.ComputedPositiveSeparator := by
  intro d a b hne
  obtain ⟨n, hn, hcn, hwn, hvn⟩ := ExponentialNormalizerProgramSemantics.fullEffectiveNormalization d a
  obtain ⟨m, hm, hcm, hwm, hvm⟩ := ExponentialNormalizerProgramSemantics.fullEffectiveNormalization d b
  let p : HeightCode := (a.depth, n)
  let q : HeightCode := (b.depth, m)
  let roots : List HeightCode := [p, q]
  have hroots : SourceFamily d roots := by
    intro r hr
    simp [roots] at hr
    rcases hr with rfl | rfl
    · exact ⟨hcn, hwn⟩
    · exact ⟨hcm, hwm⟩
  have hin : normalInputs d (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) = some (p, q) := by
    simp [normalInputs, hn, hm, p, q]
  have hfalse := (sourceDecision d a b).2.mpr hne
  have hsame : sameCode d (p, q) = false := by simpa [decisionCode, hin] using hfalse
  let T := RaySeparation.threshold d roots
  let xs := RaySeparation.rayList d roots T
  have hray := RaySeparationProof.positiveEffectiveRay d roots
  have hpos : ∀ i : Fin d, 0 < xs.getD i.val 0 := by
    intro i
    change 0 < ((RaySeparation.weights d roots).map (fun a => a * T)).getD i.val 0
    rw [map_mul_getD]
    exact (hray.2.2 i).2 T le_rfl
  refine ⟨xs, hpos, ?_, ?_, ?_⟩
  · simp [separatorCode, hin, hsame, xs, T, roots]
  · simpa [xs, RaySeparation.rayList] using hray.1
  · intro heq
    have hp := (RayFamilyClosureProof.originalMembersAndZero d roots).1 p (by simp [roots])
    have hq := (RayFamilyClosureProof.originalMembersAndZero d roots).1 q (by simp [roots])
    have hl := RayFamilyClosureProof.liftedOriginalSemantics d roots hroots
    have hcp := (hl.1 _ (hl.2 p hp).1).1
    have hcq := (hl.1 _ (hl.2 q hq).1).1
    have hneq : ¬CommonHeightEqual d (maxHeight roots) p q := by
      intro hEq
      have hcode := (ExponentialHereditaryCodecProof.faithfulness d (maxHeight roots) _ _ hcp hcq).mp hEq
      have hH : maxHeight roots = max p.1 q.1 := by simp [roots, maxHeight]
      rw [hH] at hcode
      have ht : sameCode d (p, q) = true := by simp [sameCode, hcode]
      simp [hsame] at ht
    have htuple : (fun i => ((positiveTuple d xs hpos i : PosNat) : Nat)) =
        (fun i : Fin d => (RaySeparation.weights d roots).getD i.val 0 * T) := by
      funext i
      exact map_mul_getD (RaySeparation.weights d roots) T i.val
    have hvp := hvn (positiveTuple d xs hpos)
    have hvq := hvm (positiveTuple d xs hpos)
    rw [htuple] at hvp hvq
    have hvalue : RaySeparation.originalValue d roots p T = RaySeparation.originalValue d roots q T :=
      hvp.trans (heq.trans hvq.symm)
    have hs := (RaySeparationProof.computedEventualSigns).2 d roots hroots p hp q hq T le_rfl
    have hbound := (RaySeparationProof.computedEventualSigns).1 d roots p q
    have hnzero : RaySeparation.signCode d roots p q ≠ 0 := fun h => hneq (hs.1.mp h)
    have hnone : RaySeparation.signCode d roots p q ≠ 1 := by
      intro h
      have hlt := hs.2.1.mp h
      omega
    have hntwo : RaySeparation.signCode d roots p q ≠ 2 := by
      intro h
      have hlt := hs.2.2.mp h
      omega
    omega

theorem pr_normalInputs : Primrec (fun p : Nat × List Nat × List Nat => normalInputs p.1 p.2.1 p.2.2) := by
  have ha : Primrec (fun p : Nat × List Nat × List Nat => normalizeCode p.1 p.2.1) :=
    ExponentialNormalizerProgramEffectivity.pr_normalizeCode.comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hb : Primrec (fun p : (Nat × List Nat × List Nat) × HeightCode => normalizeCode p.1.1 p.1.2.2) :=
    ExponentialNormalizerProgramEffectivity.pr_normalizeCode.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hpair : Primrec₂ (fun (p : (Nat × List Nat × List Nat) × HeightCode) (q : HeightCode) => (p.2, q)) :=
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  have hh := Primrec.option_bind ha (Primrec.option_map hb hpair).to₂
  exact hh.of_eq (by rintro ⟨d, a, b⟩; simp [normalInputs, Option.map_eq_bind])

theorem pr_sameCode : Primrec (fun p : Nat × (HeightCode × HeightCode) => sameCode p.1 p.2) := by
  have hd : Primrec (fun p : Nat × (HeightCode × HeightCode) => p.1) := Primrec.fst
  have ha : Primrec (fun p : Nat × (HeightCode × HeightCode) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : Nat × (HeightCode × HeightCode) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hH : Primrec (fun p : Nat × (HeightCode × HeightCode) => max p.2.1.1 p.2.2.1) :=
    Primrec.nat_max.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)
  have hla := RayFamilyClosureProof.pr_liftCode.comp (hd.pair (hH.pair ha))
  have hlb := RayFamilyClosureProof.pr_liftCode.comp (hd.pair (hH.pair hb))
  exact (Primrec.eq.comp hla hlb).decide

theorem pr_decisionCode : Primrec (fun p : Nat × List Nat × List Nat => decisionCode p.1 p.2.1 p.2.2) := by
  apply Primrec.option_map pr_normalInputs
  exact (pr_sameCode.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

private theorem pr_separatorRay : Primrec (fun p : Nat × (HeightCode × HeightCode) =>
    RaySeparation.rayList p.1 [p.2.1, p.2.2] (RaySeparation.threshold p.1 [p.2.1, p.2.2])) := by
  have hd : Primrec (fun p : Nat × (HeightCode × HeightCode) => p.1) := Primrec.fst
  have hr : Primrec (fun p : Nat × (HeightCode × HeightCode) => [p.2.1, p.2.2]) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
  have ht := RaySeparationProof.pr_threshold.comp (hd.pair hr)
  have hargs : Primrec (fun p : Nat × (HeightCode × HeightCode) =>
      (p.1, [p.2.1, p.2.2], RaySeparation.threshold p.1 [p.2.1, p.2.2])) := hd.pair (hr.pair ht)
  exact (RaySeparationProof.pr_rayList.comp hargs).of_eq (fun _ => rfl)

private theorem pr_separatorStep : Primrec (fun p : Nat × (HeightCode × HeightCode) =>
    if sameCode p.1 p.2 then (none : Option (List Nat)) else
      some (RaySeparation.rayList p.1 [p.2.1, p.2.2] (RaySeparation.threshold p.1 [p.2.1, p.2.2]))) := by
  exact Primrec.ite (Primrec.eq.comp pr_sameCode (Primrec.const true))
    (Primrec.const none) (Primrec.option_some.comp pr_separatorRay)

theorem pr_separatorCode : Primrec (fun p : Nat × List Nat × List Nat => separatorCode p.1 p.2.1 p.2.2) := by
  apply Primrec.option_bind pr_normalInputs
  exact (pr_separatorStep.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem actualUniformPrograms : Comparators.ExponentialIdentity.ActualUniformPrograms :=
  ⟨pr_normalInputs, pr_sameCode, pr_decisionCode, pr_separatorCode⟩

theorem exponentialIdentity : Comparators.ExponentialIdentity.Target :=
  ⟨originalFormCompleteness, sourceN4, rawInputCoverage, liftedNormalization,
    exactRawDomain, sourceDecision, computedPositiveSeparator, actualUniformPrograms⟩

end LogicLineages.ComputabilityKnowledge.ExponentialIdentityProof

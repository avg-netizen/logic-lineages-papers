module
public import LogicLineages.OrdinalComparison.MultivariateCollectedAlgebraProof
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateCollected

attribute [local irreducible] Phi actualCollapse

private theorem old_tags_induction {P : CollectedPositiveTags → Prop}
    (nil : P .nil) (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : CollectedPositiveTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (old_tags_induction nil cons rest)
termination_by tags

private theorem insert_shape (d cap : Nat) (rho : NONote) (A : CollectedPositiveNF)
    (a : Nat) (tags : CollectedPositiveTags)
    (hA : (∃ i : Nat, positiveVariableHeadIndex cap rho=some i ∧ i<d ∧ A=.mk 0 1 .nil) ∨
      (rawNoteEncode rho.1≤cap ∧ MultivariateProbeNFShape d cap A))
    (ht : MultivariateProbeTagsShape d cap tags) :
    MultivariateProbeTagsShape d cap (collectedTagInsert rho A a tags) := by
  induction tags using old_tags_induction with
  | nil =>
    by_cases ha : a=0
    · simp only [collectedTagInsert,if_pos ha,MultivariateProbeTagsShape]
    · simpa only [collectedTagInsert,if_neg ha,MultivariateProbeTagsShape,and_true] using hA
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simpa only [collectedTagInsert,if_pos ha] using ht
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · simpa only [collectedTagInsert,if_neg ha,if_pos hl,MultivariateProbeTagsShape] using And.intro hA ht
    by_cases he : collectedTagKey rho A=collectedTagKey sigma B
    · simpa only [collectedTagInsert,if_neg ha,if_neg hl,if_pos he,MultivariateProbeTagsShape] using ht
    · rw [collectedTagInsert,if_neg ha,if_neg hl,if_neg he]
      exact And.intro ht.1 (ih ht.2)

private theorem merge_shape (d cap : Nat) (left right : CollectedPositiveTags)
    (hl : MultivariateProbeTagsShape d cap left) (hr : MultivariateProbeTagsShape d cap right) :
    MultivariateProbeTagsShape d cap (collectedTagsMerge left right) := by
  induction left using old_tags_induction with
  | nil => exact hr
  | cons rho A a rest ih =>
    exact insert_shape d cap rho A a _ hl.1 (ih hl.2)

private theorem add_shape (d cap : Nat) (A B : CollectedPositiveNF)
    (hA : MultivariateProbeNFShape d cap A) (hB : MultivariateProbeNFShape d cap B) :
    MultivariateProbeNFShape d cap (collectedPositiveAdd A B) := by
  cases A with
  | mk c b tags =>
    cases B with
    | mk e f rest =>
      exact ⟨by simpa only [hA.1,hB.1],merge_shape d cap tags rest hA.2 hB.2⟩

private theorem source_shape (d cap : Nat) (E : MultivariatePositiveExpr) :
    multivariatePositiveValid d E → multivariatePositiveEncode E≤cap →
      MultivariateProbeNFShape d cap (collectedPositiveNormalize (multivariatePositiveProbe cap E)) := by
  induction E with
  | constant c => intro _ _; exact ⟨rfl,True.intro⟩
  | input i =>
    intro hv _
    change 0=0 ∧
      ((∃ j : Nat, positiveVariableHeadIndex cap (positiveVariableHead cap i)=some j ∧
        j<d ∧ CollectedPositiveNF.mk 0 1 .nil=.mk 0 1 .nil) ∨ _) ∧ True
    exact ⟨rfl,Or.inl ⟨i,(MultivariateFreshProbe.head_source.1 cap i).2.2.2,hv,rfl⟩,True.intro⟩
  | add E F ihE ihF =>
    intro hv hc
    have hl := Nat.left_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
    have hr := Nat.right_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
    have he : multivariatePositiveEncode E≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    have hf : multivariatePositiveEncode F≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    exact add_shape d cap _ _ (ihE hv.1 he) (ihF hv.2 hf)
  | head rho E ih =>
    intro hv hc
    have hl := Nat.left_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
    have hr := Nat.right_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
    have hh : rawNoteEncode rho.1≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    have he : multivariatePositiveEncode E≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    by_cases hz : collectedPositiveSupport (collectedPositiveNormalize (multivariatePositiveProbe cap E))=false
    · simp only [multivariatePositiveProbe,collectedPositiveNormalize,if_pos hz,
        MultivariateProbeNFShape,MultivariateProbeTagsShape,and_true]
    · simp only [multivariatePositiveProbe,collectedPositiveNormalize,if_neg hz,
        MultivariateProbeNFShape,MultivariateProbeTagsShape,and_true]
      exact ⟨True.intro,Or.inr ⟨hh,ih hv.2.2 he⟩⟩

theorem probe_shape : Targets.MultivariateCollectedProbeShape := source_shape

mutual
  private theorem decode_form_value (d cap : Nat) (A : CollectedPositiveNF)
      (hs : MultivariateProbeNFShape d cap A) (rho : Nat → Nat) :
      actualMultivariateCollectedValue (decodeMultivariateCollected cap A) rho=
        interpretedCollectedEval (positiveRetractedHead cap rho) A 0 := by
    cases A with
    | mk c b tags =>
      have hb : b=0 := hs.1
      subst b
      rw [decodeMultivariateCollected,additive.1]
      simpa only [actualMultivariateCollectedValue,multivariateCoefficientValue,
        actualMultivariateCollectedTagsValue,interpretedCollectedEval,Nat.zero_mul,
        Nat.add_zero] using congrArg (fun n => c+n) (decode_tags_value d cap tags hs.2 rho)
  private theorem decode_tags_value (d cap : Nat) (tags : CollectedPositiveTags)
      (hs : MultivariateProbeTagsShape d cap tags) (rho : Nat → Nat) :
      actualMultivariateCollectedValue (decodeMultivariateCollectedTags cap tags) rho=
        interpretedCollectedTagsEval (positiveRetractedHead cap rho) tags 0 := by
    cases tags with
    | nil => simp [decodeMultivariateCollectedTags,actualMultivariateCollectedValue,
        multivariateCoefficientValue,actualMultivariateCollectedTagsValue,interpretedCollectedTagsEval]
    | cons head A a rest =>
      have ht := decode_tags_value d cap rest hs.2 rho
      cases hi : positiveVariableHeadIndex cap head with
      | some i =>
        simp only [decodeMultivariateCollectedTags,hi]
        rw [additive.1]
        simpa only [actualMultivariateCollectedValue,actualMultivariateCollectedTagsValue,
          additive.2,multivariateCoefficientValue,Nat.zero_add,Nat.add_zero,
          interpretedCollectedTagsEval,positiveRetractedHead,hi,Option.map_some,Option.getD_some] using
          congrArg (fun n => a*rho i+n) ht
      | none =>
        have hA : MultivariateProbeNFShape d cap A := by
          rcases hs.1 with ⟨i,he,_⟩ | ⟨_,ha⟩
          · rw [hi] at he; cases he
          · exact ha
        have hv := decode_form_value d cap A hA rho
        simp only [decodeMultivariateCollectedTags,hi]
        rw [additive.1]
        simpa only [actualMultivariateCollectedValue,actualMultivariateCollectedTagsValue,
          multivariateCoefficientValue,Nat.zero_add,Nat.add_zero,interpretedCollectedTagsEval,
          positiveRetractedHead,hi,Option.map_none,Option.getD_none,hv] using
          congrArg (fun n => a*actualProfileHead head
            (interpretedCollectedEval (positiveRetractedHead cap rho) A 0)+n) ht
end

theorem decode_semantics : Targets.MultivariateCollectedDecodeSemantics := decode_form_value

theorem source_semantics : Targets.MultivariateCollectedSourceSemantics := by
  intro d cap E hv hc rho
  exact (decode_semantics d cap _ (probe_shape d cap E hv hc) rho).trans
    (MultivariateFreshProbe.retraction d cap E hv hc rho 0)

end LogicLineages.OrdinalComparison.MultivariateCollected

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedMarkCertificate NumberedMultisetCertificate

private theorem replacementSound {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (removed inserted : List (Packed (Fin n) arity Gamma)) :
    ∀ witnesses,replacementTest removed inserted witnesses=true →
      ∀ q∈inserted,∃ s∈removed,PrimitiveMark (Fin n) arity Gamma s q := by
  induction inserted with
  | nil => intro witnesses h q hq; cases hq
  | cons q rest ih =>
    intro witnesses h
    cases witnesses with
    | nil => simp [replacementTest] at h
    | cons witness witnesses =>
      obtain ⟨index,label⟩ := witness
      cases he : removed[index]? with
      | none => simp [replacementTest,he] at h
      | some s =>
        have hh : markTarget label s=some q ∧ replacementTest removed rest witnesses=true := by
          simpa [replacementTest,he] using h
        intro r hr
        rcases List.mem_cons.mp hr with hr|hr
        · subst r
          exact ⟨s,List.mem_of_getElem? he,(NumberedMarkCertificateProof.typedMarkCheck n arity Gamma s q).mp ⟨label,hh.1⟩⟩
        · exact ih witnesses hh.2 r hr

private theorem replacementComplete {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (removed inserted : List (Packed (Fin n) arity Gamma)) :
    (∀ q∈inserted,∃ s∈removed,PrimitiveMark (Fin n) arity Gamma s q) →
      ∃ witnesses,replacementTest removed inserted witnesses=true := by
  induction inserted with
  | nil => intro h; exact ⟨[],rfl⟩
  | cons q rest ih =>
    intro h
    obtain ⟨s,hs,hm⟩ := h q (by simp)
    obtain ⟨index,he⟩ := List.mem_iff_getElem?.mp hs
    obtain ⟨label,hl⟩ := (NumberedMarkCertificateProof.typedMarkCheck n arity Gamma s q).mpr hm
    obtain ⟨witnesses,hw⟩ := ih (fun r hr => h r (by simp [hr]))
    exact ⟨(index,label)::witnesses,by simp [replacementTest,he,hl,hw]⟩

theorem replacementCertificates : NumberedMultisetCertificateTargets.ActualReplacementCertificates := by
  intro n arity Gamma removed inserted
  exact ⟨fun ⟨w,h⟩ => replacementSound removed inserted w h,replacementComplete removed inserted⟩

theorem occurrenceWitnessCount : NumberedMultisetCertificateTargets.ActualOccurrenceWitnessCount := by
  intro n arity Gamma removed inserted
  induction inserted with
  | nil =>
    intro witnesses h
    cases witnesses with
    | nil => rfl
    | cons => simp [replacementTest] at h
  | cons q rest ih =>
    intro witnesses h
    cases witnesses with
    | nil => simp [replacementTest] at h
    | cons witness witnesses =>
      obtain ⟨index,label⟩ := witness
      cases he : removed[index]? with
      | none => simp [replacementTest,he] at h
      | some s =>
        have hh : markTarget label s=some q ∧ replacementTest removed rest witnesses=true := by
          simpa [replacementTest,he] using h
        simpa using congrArg Nat.succ (ih witnesses hh.2)

theorem primitiveMultisetCertificates : NumberedMultisetCertificateTargets.ActualPrimitiveMultisetCertificates := by
  intro n arity Gamma source target
  constructor
  · rintro ⟨c,h⟩
    have hh : (source.Perm (c.kept++c.removed) ∧ target.Perm (c.kept++c.inserted) ∧ c.removed≠[]) ∧
        replacementTest c.removed c.inserted c.witnesses=true := by simpa [multisetTest] using h
    exact ⟨c.kept,c.removed,c.inserted,hh.1.1,hh.1.2.1,hh.1.2.2,replacementSound _ _ _ hh.2⟩
  · rintro ⟨kept,removed,inserted,hs,ht,hn,hr⟩
    obtain ⟨w,hw⟩ := replacementComplete removed inserted hr
    exact ⟨⟨kept,removed,inserted,w⟩,by simp [multisetTest,hs,ht,hn,hw]⟩

theorem multisetCertificateConfinement : NumberedMultisetCertificateTargets.ActualMultisetCertificateConfinement := by
  intro n arity symbols S Gamma source target certificate h hg q hq
  obtain ⟨kept,removed,inserted,hs,ht,hn,hr⟩ :=
    (primitiveMultisetCertificates n arity Gamma source target).mp ⟨certificate,h⟩
  rcases List.mem_append.mp (ht.mem_iff.mp hq) with hk|hi
  · exact hg q (hs.mem_iff.mpr (List.mem_append.mpr (Or.inl hk)))
  · obtain ⟨s,hsm,hm⟩ := hr q hi
    have hsg := hg s (hs.mem_iff.mpr (List.mem_append.mpr (Or.inr hsm)))
    cases hm with
    | mk label a b he =>
      exact NumberedUniverseBindingProof.markGood (fun t => t∈S) (HeadInWindow arity symbols S) label a b he hsg

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateProof

module
public import LogicLineages.PermittedControl.HighestPieceCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem candidate_decode_facts (mu nu E : NONote) (n : Nat)
    (hn : n ∈ highestPieceCandidates (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1)) :
    actualOrdinalNorm (rawNoteDecode n).repr ≤ 2+actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr ∧
    2 ≤ (rawNoteDecode n).repr ∧ (rawNoteDecode n).repr < E.1.repr ∧
    relativeProfile mu.1.repr (rawNoteDecode n).repr ≠ relativeProfile nu.1.repr (rawNoteDecode n).repr := by
  let a : NONote := ⟨rawNoteDecode n,profile_candidates_normal _ _ _ n hn⟩
  have h := (profile_candidates_iff mu nu E a).mp
  have hc : rawNoteEncode a.1=n := rawNoteEncodeDecode n
  rw [hc] at h
  exact h hn

private theorem profile_nonzero_candidate (mu nu E : NONote) (x : Ordinal.{0})
    (hx : 2 ≤ x) (hxE : x < E.1.repr)
    (hne : relativeProfile mu.1.repr x ≠ relativeProfile nu.1.repr x) :
    ∃ n ∈ highestPieceCandidates (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1),
      SameProfilePiece mu.1.repr nu.1.repr x (rawNoteDecode n).repr := by
  have hm := normalRepresentationSound mu
  have hn := normalRepresentationSound nu
  have he := normalRepresentationSound E
  obtain ⟨y,hy,hpiece⟩ := jointProfileFiniteCover mu.1.repr nu.1.repr E.1.repr x hm hn he hx hxE
  have hb := jointProfileCoverBound mu.1.repr nu.1.repr E.1.repr hm hn he y hy
  have hyd := of_decide_eq_true (List.mem_filter.mp hy).2
  have hcost := jointProfilePieceConstant _ _ _ _ hm hn hpiece
  have hyne : relativeProfile mu.1.repr y ≠ relativeProfile nu.1.repr y := by
    rwa [hcost.1,hcost.2] at hne
  obtain ⟨a,ha⟩ := normalRepresentationComplete y hb.1
  refine ⟨rawNoteEncode a.1,?_,?_⟩
  · apply (profile_candidates_iff mu nu E a).mpr
    simpa only [ha] using And.intro hb.2 (And.intro hyd.1 (And.intro hyd.2 hyne))
  · rw [rawNoteDecodeEncode a.1,ha]
    exact hpiece

 theorem highestPieceNone : Targets.HighestPieceNone := by
  intro mu nu E
  constructor
  · intro hnone x hx hxE
    by_contra hne
    obtain ⟨n,hn,_⟩ := profile_nonzero_candidate mu nu E x hx hxE hne
    have hl := (largest_profile_none _).mp hnone
    rw [hl] at hn
    exact List.not_mem_nil hn
  · intro heq
    apply (largest_profile_none _).mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n hn
    have h := candidate_decode_facts mu nu E n hn
    exact h.2.2.2 (heq _ h.2.1 h.2.2.1)

 theorem highestPieceSome : Targets.HighestPieceSome := by
  intro mu nu E n hn
  have hs := largest_profile_some _ (profile_candidates_normal _ _ _) n hn
  have hnf := profile_candidates_normal _ _ _ n hs.1
  let a : NONote := ⟨rawNoteDecode n,hnf⟩
  have hfacts := candidate_decode_facts mu nu E n hs.1
  refine ⟨hnf,normalRepresentationSound a,hfacts.1,hfacts.2.1,hfacts.2.2.1,hfacts.2.2.2,hs.2,?_,?_⟩
  · intro x hx hxE hne hnx
    by_contra hpiece
    obtain ⟨m,hm,hxm⟩ := profile_nonzero_candidate mu nu E x hx hxE hne
    have hnm := jointProfilePieceOrder _ _ _ _ _ hnx hpiece hxm
    exact (not_lt_of_ge (hs.2 m hm)) hnm
  · intro x hx
    have hcost := jointProfilePieceConstant _ _ _ _ (normalRepresentationSound mu) (normalRepresentationSound nu) hx
    have hm := rawProfileCorrect mu a
    have hv := rawProfileCorrect nu a
    change rawProfileCode (rawNoteEncode mu.1) (rawNoteEncode (rawNoteDecode n)) = relativeProfile mu.1.repr (rawNoteDecode n).repr at hm
    change rawProfileCode (rawNoteEncode nu.1) (rawNoteEncode (rawNoteDecode n)) = relativeProfile nu.1.repr (rawNoteDecode n).repr at hv
    rw [rawNoteEncodeDecode n] at hm hv
    rw [hm,hv,hcost.1,hcost.2]

 theorem highestPieceFoundation : Targets.HighestPieceFoundation :=
  ⟨jointProfileCoverBound,jointProfilePieceOrder,highestPieceEffective,highestPieceNone,highestPieceSome⟩

end LogicLineages.PermittedControl

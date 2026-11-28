module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOwnCoverTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAdmissionChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCoverBoundsChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverGrammarProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowHeadEnumerationProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOwnCoverChecks
open NumberedWindowOwnCoverTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryCoverSyntax
open NumberedWindowAdmissionTargets (termGuard typesIn window)
open NumberedWindowArithmeticTermCode (encodeTerm decodeTerm)
open NumberedWindowHeadEnumerationTargets (admittedHeads)

private theorem ownSymbolicCover (S : Spine.Signature) (K : List Ty) (q : NTerm)
    (guard : termGuard S K q = true) : q ∈ cover S K q := by
  simp only [termGuard,typesIn,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    NumberedWindowHeadEnumerationProof.bit] at guard
  let b := termBounds q
  have joined : NArgs.cons q .nil ∈ (grammar (admittedHeads S K) K b.numeral (b.nodes+1)).2 :=
    NumberedWindowPrimaryCoverGrammarProof.args S K (.cons q .nil) b.numeral (b.nodes+1)
      (by simpa [argsSupport] using guard.1)
      (by simpa [argsHeads] using guard.2)
      (by simp [argsBounds,b])
      (by simp [argsBounds,b])
  let layer := grammar (admittedHeads S K) K b.numeral b.nodes
  change NArgs.cons q .nil ∈ argumentCells layer.1 layer.2 at joined
  have expanded : NArgs.cons q .nil ∈ layer.1.flatMap (fun x => layer.2.map (NArgs.cons x)) := by
    rcases List.mem_cons.mp joined with same | member
    · cases same
    · exact member
  obtain ⟨x,hx,tailMember⟩ := List.mem_flatMap.mp expanded
  obtain ⟨_,_,same⟩ := List.mem_map.mp tailMember
  have inOriginal : x ∈ cover S K q := hx
  rw [(NArgs.cons.inj same).1] at inOriginal
  exact inOriginal

theorem exact_AdmittedOwnCover : ExactAdmittedOwnCover := by
  intro S K raw admitted
  rw [NumberedWindowAdmissionChecks.exact_DecodedAdmission S K raw] at admitted
  cases read : decodeTerm raw with
  | none => simp [read] at admitted
  | some q =>
    have guard : termGuard S K q = true := by simpa only [read,Option.any_some] using admitted
    have sameCode : encodeTerm q = raw :=
      (NumberedWindowArithmeticTermCodeChecks.exact_TermCodec.1 raw q).mp read
    have sameCover := NumberedWindowArithmeticCoverBoundsChecks.exact_SourceSelectedCover S K raw
    change NumberedWindowCoverBoundsAlgorithm.cover (window S K).2 _ raw = _ at sameCover
    rw [sameCover,read]
    exact ⟨_,rfl,List.mem_map.mpr ⟨q,ownSymbolicCover S K q guard,sameCode⟩⟩

#print axioms exact_AdmittedOwnCover

end LogicLineages.PersistentMarking.NumberedWindowOwnCoverChecks

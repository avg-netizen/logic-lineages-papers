module
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixes
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualRawCanonicalZeroReplay (AnswerCode SequenceCode stepCode replayCode)

private theorem memChildren (p q : Candidate) :
    q ∈ children p ↔ ∃ a ∈ available p.2, stepCode (p.2,a) = some q.2 ∧ q.1 = p.1 ++ [a] := by
  constructor
  · intro member
    change q ∈ (available p.2).filterMap (fun tape => extendCandidate (p,tape)) at member
    obtain ⟨a,used,emits⟩ := List.mem_filterMap.mp member
    unfold extendCandidate at emits
    cases h : stepCode (p.2,a) with
    | none => simp [h] at emits
    | some out =>
      have eq : (p.1++[a],out) = q := Option.some.inj (by simpa [h] using emits)
      subst q
      exact ⟨a,used,h,rfl⟩
  · rintro ⟨a,used,ok,eq⟩
    change q ∈ (available p.2).filterMap (fun tape => extendCandidate (p,tape))
    refine List.mem_filterMap.mpr ⟨a,used,?_⟩
    unfold extendCandidate
    rw [ok]
    exact congrArg some (Prod.ext eq.symm rfl)

theorem exactRawZeroPrefixLevels : ExactRawZeroPrefixLevels := by
  intro start n
  induction n with
  | zero =>
    intro entry
    constructor
    · intro member
      have eq : entry = ([],start) := List.mem_singleton.mp member
      subst entry
      exact ⟨CandidatePath.nil,rfl⟩
    · rintro ⟨path,hlen⟩
      rcases entry with ⟨tapes,st⟩
      change tapes.length = 0 at hlen
      cases path with
      | nil => exact List.mem_cons_self
      | @snoc past s t a prev used ok =>
        change (past++[a]).length = 0 at hlen
        have impossible : past.length + 1 = 0 := by
          simpa only [List.length_append,List.length_cons,List.length_nil] using hlen
        omega
  | succ n ih =>
    intro entry
    constructor
    · intro mem
      change entry ∈ (level start n).flatMap children at mem
      obtain ⟨prior,hp,child⟩ := List.mem_flatMap.mp mem
      obtain ⟨a,used,ok,eq⟩ := (memChildren prior entry).mp child
      obtain ⟨path,priorLength⟩ := (ih prior).mp hp
      rw [eq]
      exact ⟨CandidatePath.snoc path used ok,by simp [priorLength]⟩
    · rintro ⟨path,hlen⟩
      rcases entry with ⟨tapes,st⟩
      change tapes.length = n+1 at hlen
      cases path with
      | nil => simp at hlen
      | @snoc past s t a prev used ok =>
        change (past ++ [a]).length = n+1 at hlen
        have eqSucc : past.length + 1 = n+1 := by
          simpa only [List.length_append,List.length_cons,List.length_nil] using hlen
        have priorLength : past.length = n := Nat.add_right_cancel eqSucc
        change (past++[a],st) ∈ (level start n).flatMap children
        refine List.mem_flatMap.mpr ⟨(past,s),(ih (past,s)).mpr ⟨prev,priorLength⟩,?_⟩
        exact (memChildren (past,s) (past++[a],st)).mpr ⟨a,used,ok,rfl⟩

theorem exactRawZeroPrefixEnumeration : ExactRawZeroPrefixEnumeration := by
  intro fuel start entry
  constructor
  · intro mem
    change entry ∈ (List.range (fuel+1)).flatMap (level start) at mem
    obtain ⟨n,within,member⟩ := List.mem_flatMap.mp mem
    obtain ⟨path,eq⟩ := (exactRawZeroPrefixLevels start n entry).mp member
    refine ⟨path,?_⟩
    rw [eq]
    exact Nat.le_of_lt_succ (List.mem_range.mp within)
  · rintro ⟨path,within⟩
    change entry ∈ (List.range (fuel+1)).flatMap (level start)
    exact List.mem_flatMap.mpr ⟨entry.1.length,List.mem_range.mpr (Nat.lt_succ_of_le within),
      (exactRawZeroPrefixLevels start entry.1.length entry).mpr ⟨path,rfl⟩⟩

private theorem successfulReplay (start : RawSyntax) (tapes : SequenceCode) (out : RawSyntax)
    (path : CandidatePath start tapes out) : replayCode (tapes,start) = some out := by
  induction path with
  | nil => rfl
  | @snoc past s t answer prev _ hit ih =>
    change past.foldl ActualRawCanonicalZeroReplay.advanceCode (some start) = some s at ih
    change (past++[answer]).foldl ActualRawCanonicalZeroReplay.advanceCode (some start) = some t
    rw [List.foldl_append,ih]
    exact hit

theorem exactRawZeroPrefixReplay : ExactRawZeroPrefixReplay := by
  intro fuel start entry member
  have valid := (exactRawZeroPrefixEnumeration fuel start entry).mp member
  exact ⟨successfulReplay start entry.1 entry.2 valid.1,valid.2⟩

end LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixes

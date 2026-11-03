module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceCounterexampleInversionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticObstructionsProof
open Source Source.SourceMarkedSyntax RecursiveComparison OrdinaryBetaTransitivityDiagnostic
open MarkedSourceCounterexampleInversionProof

theorem markedZeroNotH : ¬Weak Nat arity above []
    ⟨.ground,.marked (.ranked 0) .ground .nil [] .nil⟩ ⟨.ground,h⟩ := by
  intro hw
  rcases markedInversion above _ _ hw 0 .nil 1 .nil rfl rfl with hp | ⟨he,hm⟩ | ⟨v,hv,hvt⟩
  · change 1<0 at hp; omega
  · cases he
  · cases hv

theorem zeroNotH : ¬Weak Nat arity above [] ⟨.ground,z⟩ ⟨.ground,h⟩ := by
  intro hw
  rcases ordinaryInversion above _ _ hw 0 .nil 1 .nil rfl rfl with he | hm
  · cases he
  · exact markedZeroNotH hm

theorem zeroNotStrictH : ¬Strict Nat arity above [] ⟨.ground,z⟩ ⟨.ground,h⟩ := by
  intro hs
  cases hs with
  | mark a marked b hm hw =>
    have he : MarkedTerm.marked (arity := arity) (.ranked 0) .ground .nil [] .nil=marked := Option.some.inj hm
    subst marked
    exact markedZeroNotH hw

theorem qNotStrictH : ¬Strict Nat arity above [] ⟨.ground,q⟩ ⟨.ground,h⟩ := by
  intro hs
  cases hs with
  | mark a marked b hm hw => cases hm

theorem constantNotU (i : Nat) (hi : i=0 ∨ i=1) (ha : arity i=0) :
    ¬Weak Nat arity above [] ⟨.ground,.ordinary (.ranked i) (by simp only [headArguments,ha,List.replicate_zero]; exact .nil)⟩ ⟨.ground,u⟩ := by
  have marked : ¬Weak Nat arity above []
      ⟨.ground,.marked (.ranked i) .ground (by simp only [headArguments,ha,List.replicate_zero]; exact .nil) [] .nil⟩ ⟨.ground,u⟩ := by
    intro hw
    rcases markedInversion above _ _ hw i (by rw [ha]; exact .nil) 3 (.cons h (.cons h .nil)) rfl rfl with hp | ⟨he,hm⟩ | ⟨v,hv,hvt⟩
    · change 3<i at hp; rcases hi with rfl | rfl <;> omega
    · change HeadClass.ranked i=HeadClass.ranked 3 at he
      have he' : i=3 := HeadClass.ranked.inj he
      rcases hi with rfl | rfl <;> omega
    · have hnil : argumentList (show Arguments Nat arity [] (List.replicate (arity i) .ground) from (by rw [ha]; exact .nil))=[] := by rcases hi with rfl | rfl <;> rfl
      rw [hnil] at hv; cases hv
  intro hw
  rcases ordinaryInversion above _ _ hw i (by rw [ha]; exact .nil) 3 (.cons h (.cons h .nil)) rfl rfl with he | hm
  · change HeadClass.ranked i=HeadClass.ranked 3 at he
    have he' : i=3 := HeadClass.ranked.inj he
    rcases hi with rfl | rfl <;> omega
  · exact marked hm

theorem zeroNotU : ¬Weak Nat arity above [] ⟨.ground,z⟩ ⟨.ground,u⟩ := constantNotU 0 (.inl rfl) rfl
theorem hNotU : ¬Weak Nat arity above [] ⟨.ground,h⟩ ⟨.ground,u⟩ := constantNotU 1 (.inr rfl) rfl

theorem kNotU : ¬Weak Nat arity above [] ⟨.ground,k⟩ ⟨.ground,u⟩ := by
  have marked : ¬Weak Nat arity above []
      ⟨.ground,.marked (.ranked 2) .ground (.cons h .nil) [] .nil⟩ ⟨.ground,u⟩ := by
    intro hw
    rcases markedInversion above _ _ hw 2 (.cons h .nil) 3 (.cons h (.cons h .nil)) rfl rfl with hp | ⟨he,hm⟩ | ⟨v,hv,hvt⟩
    · change 3<2 at hp; omega
    · cases he
    · change v∈[⟨.ground,h⟩] at hv
      have he := List.mem_singleton.mp hv
      subst v
      exact hNotU hvt
  intro hw
  rcases ordinaryInversion above _ _ hw 2 (.cons h .nil) 3 (.cons h (.cons h .nil)) rfl rfl with he | hm
  · cases he
  · exact marked hm

theorem matchLength {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (hm : WeakMatch Symbol arity above Gamma ss ts) : ss.length=ts.length := by
  induction ss generalizing ts with
  | nil => cases hm; rfl
  | cons s ss ih => cases hm with
    | cons s t ss ts hw hr => exact congrArg Nat.succ (ih hr)

theorem noWeakMatching (matched : List (Packed Nat arity []))
    (hp : ([⟨.ground,h⟩,⟨.ground,h⟩] : List (Packed Nat arity [])).Perm matched)
    (hm : WeakMatch Nat arity above [] [⟨.ground,q⟩,⟨.ground,z⟩] matched) : False := by
  cases hm with
  | cons sq v ss vs hq hr => cases hr with
    | cons sz w rest ws hz ht =>
      have hw : w∈([⟨.ground,h⟩,⟨.ground,h⟩] : List (Packed Nat arity [])) := hp.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hw
      subst w
      exact zeroNotH hz

theorem noStrictMultiset : ¬StrictMultiset Nat arity above []
    [⟨.ground,q⟩,⟨.ground,z⟩] [⟨.ground,h⟩,⟨.ground,h⟩] := by
  intro hm
  cases hm with
  | replace ss ts kept retained removed inserted hs ht hn hmatch hr =>
    have hinserted : inserted=[] := by
      cases inserted with
      | nil => rfl
      | cons v rest =>
        cases hr with
        | cons removed source target tail hmem hstrict hrest =>
          have hv : v∈([⟨.ground,h⟩,⟨.ground,h⟩] : List (Packed Nat arity [])) := ht.symm.subset (List.mem_append_right _ (List.mem_cons_self ..))
          simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hv
          subst v
          have hsrc : source∈([⟨.ground,q⟩,⟨.ground,z⟩] : List (Packed Nat arity [])) := hs.symm.subset (List.mem_append_right _ hmem)
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hsrc
          rcases hsrc with he | he
          · subst source; exact (qNotStrictH hstrict).elim
          · subst source; exact (zeroNotStrictH hstrict).elim
    have hlen1 := hs.length_eq
    have hlen2 := ht.length_eq
    have hlen3 := matchLength above hmatch
    have hpos : 0<removed.length := by cases removed with
      | nil => exact (hn rfl).elim
      | cons a rest => exact Nat.zero_lt_succ _
    rw [hinserted] at hlen2
    simp only [List.length_cons,List.length_nil,List.length_append] at hlen1 hlen2
    omega

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticObstructionsProof

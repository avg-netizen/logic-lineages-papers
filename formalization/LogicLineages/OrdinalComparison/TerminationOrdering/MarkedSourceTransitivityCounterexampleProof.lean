module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexampleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceCounterexampleInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEmbeddingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexampleProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison SourceUnmarked
open MarkedSourceTransitivityCounterexample MarkedSourceCounterexampleInversionProof

abbrev args (n : Nat) (a : Ground) := groundArguments (arity n) (fun _ => a)

theorem singletonStrict {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (a b : Packed Symbol arity Gamma)
    (h : StrictMultiset Symbol arity above Gamma [a] [b]) : Strict Symbol arity above Gamma a b := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hm hr =>
    have hlen := hs.length_eq
    simp only [List.length_cons,List.length_nil,List.length_append] at hlen
    have hpos : 0<removed.length := by
      cases removed with
      | nil => exact (hn rfl).elim
      | cons a rest => exact Nat.zero_lt_succ _
    have hk : kept=[] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    subst kept
    cases hm
    have hremoved : removed=[a] := (by simpa only [List.nil_append] using hs.symm : removed.Perm [a]).eq_singleton
    have hinserted : inserted=[b] := (by simpa only [List.nil_append] using ht.symm : inserted.Perm [b]).eq_singleton
    subst removed
    subst inserted
    cases hr with
    | cons removed p t rest hp hs hr =>
      have he : p=a := List.mem_singleton.mp hp
      subst p
      exact hs

theorem extendedSteps : MarkedSourceTransitivityCounterexampleTargets.ActualExtendedSteps := by
  have hz : Weak Nat arity above [] ⟨.ground,z⟩ ⟨.ground,z⟩ := .fun_ (.ranked 0) (.ranked 0) (args 0 z) (args 0 z) [] rfl rfl (.refl _) .nil
  have hk : Weak Nat arity above [] ⟨.ground,k⟩ ⟨.ground,k⟩ :=
    .fun_ (.ranked 1) (.ranked 1) (args 1 z) (args 1 z) [⟨.ground,z⟩] rfl rfl (.refl _) (.cons _ _ _ _ hz .nil)
  have hKz : Weak Nat arity above [] ⟨.ground,.marked (.ranked 1) .ground
      (by change Arguments Nat arity [] [.ground]; exact .cons z .nil) [] .nil⟩ ⟨.ground,z⟩ :=
    .select (.ranked 1) (args 1 z) [] .nil [] z z z rfl (by simp [args,arity,groundArguments,argumentList]) rfl hz
  have hkz : Weak Nat arity above [] ⟨.ground,k⟩ ⟨.ground,z⟩ := .put (.ranked 1) (args 1 z) z hKz
  have hqk : Weak Nat arity above [] ⟨.ground,q⟩ ⟨.ground,k⟩ := by
    change Weak Nat arity above [] ⟨.ground,MarkedTerm.marked (arity := arity) (.ranked 1) .ground (args 1 k) [] .nil⟩ ⟨.ground,k⟩
    exact .select (.ranked 1) (args 1 k) [] .nil [] k k k rfl (by simp [args,arity,groundArguments,argumentList]) rfl hk
  have hsT : SourceExtendedComparison.Weak Nat arity above [] ⟨.ground,s⟩ ⟨.ground,t⟩ :=
    .in_ (.ranked 2) (.ranked 2) (args 2 q) (args 2 k) [] .nil [] .nil [⟨.ground,k⟩] rfl (.refl _)
      (.cons _ _ _ _ (SourceExtendedEmbeddingProof.weakEmbedding hqk) .nil) .nil
  have htz : Weak Nat arity above [] ⟨.ground,t⟩ ⟨.ground,z⟩ := by
    change Weak Nat arity above [] ⟨.ground,MarkedTerm.marked (arity := arity) (.ranked 2) .ground (args 2 k) [] .nil⟩ ⟨.ground,z⟩
    exact .select (.ranked 2) (args 2 k) [] .nil [] k k z rfl (by simp [args,arity,groundArguments,argumentList]) rfl hkz
  have hstrict : SourceExtendedComparison.Strict Nat arity above [] ⟨.ground,k⟩ ⟨.ground,z⟩ :=
    .mark k (.marked (.ranked 1) .ground (by change Arguments Nat arity [] [.ground]; exact .cons z .nil) [] .nil) z rfl (SourceExtendedEmbeddingProof.weakEmbedding hKz)
  have hmulti : SourceExtendedComparison.StrictMultiset Nat arity above [] [⟨.ground,k⟩] [⟨.ground,z⟩] :=
    .replace _ _ [] [] [⟨.ground,k⟩] [⟨.ground,z⟩] (.refl _) (.refl _) (by intro h; cases h) .nil
      (.cons _ _ _ _ (List.mem_cons_self ..) hstrict (.nil _))
  have htu : SourceExtendedComparison.Weak Nat arity above [] ⟨.ground,t⟩ ⟨.ground,u⟩ :=
    .stat (.ranked 2) (.ranked 2) (args 2 k) [] .nil (args 2 z) rfl hmulti
      (by intro p hp; change p∈[⟨.ground,z⟩] at hp; have he := List.mem_singleton.mp hp; subst p; exact SourceExtendedEmbeddingProof.weakEmbedding htz)
  have hOrdZ : Unmarked Nat arity [] z := .ordinary (.ranked 0) (args 0 z) .nil
  exact ⟨hsT,htu,.ordinary (.ranked 2) (args 2 z) (.cons z .nil hOrdZ .nil)⟩

theorem originalFailure : MarkedSourceTransitivityCounterexampleTargets.ActualOriginalFailure := by
  have markedZ : ¬ Weak Nat arity above [] ⟨.ground,.marked (.ranked 0) .ground .nil [] .nil⟩ ⟨.ground,u⟩ := by
    intro h
    rcases markedInversion above _ _ h 0 .nil 2 (args 2 z) rfl rfl with hp | ⟨he,hm⟩ | ⟨p,hp,hw⟩
    · change 2<0 at hp; omega
    · cases he
    · cases hp
  have ordinaryZ : ¬ Weak Nat arity above [] ⟨.ground,z⟩ ⟨.ground,u⟩ := by
    intro h
    rcases ordinaryInversion above _ _ h 0 .nil 2 (args 2 z) rfl rfl with he | hw
    · cases he
    · exact markedZ hw
  have markedKz : ¬ Weak Nat arity above [] ⟨.ground,.marked (.ranked 1) .ground
      (by change Arguments Nat arity [] [.ground]; exact .cons z .nil) [] .nil⟩ ⟨.ground,u⟩ := by
    intro h
    rcases markedInversion above _ _ h 1 (args 1 z) 2 (args 2 z) rfl rfl with hp | ⟨he,hm⟩ | ⟨p,hp,hw⟩
    · change 2<1 at hp; omega
    · cases he
    · change p∈[⟨.ground,z⟩] at hp
      have he := List.mem_singleton.mp hp
      subst p
      exact ordinaryZ hw
  have ordinaryKz : ¬ Weak Nat arity above [] ⟨.ground,k⟩ ⟨.ground,u⟩ := by
    intro h
    rcases ordinaryInversion above _ _ h 1 (args 1 z) 2 (args 2 z) rfl rfl with he | hw
    · cases he
    · exact markedKz hw
  have markedKk : ¬ Weak Nat arity above [] ⟨.ground,q⟩ ⟨.ground,u⟩ := by
    intro h
    rcases markedInversion above _ _ h 1 (args 1 k) 2 (args 2 z) rfl rfl with hp | ⟨he,hm⟩ | ⟨p,hp,hw⟩
    · change 2<1 at hp; omega
    · cases he
    · change p∈[⟨.ground,k⟩] at hp
      have he := List.mem_singleton.mp hp
      subst p
      exact ordinaryKz hw
  intro h
  rcases markedInversion above _ _ h 2 (args 2 q) 2 (args 2 z) rfl rfl with hp | ⟨he,hm⟩ | ⟨p,hp,hw⟩
  · change 2<2 at hp; exact Nat.lt_irrefl 2 hp
  · change StrictMultiset Nat arity above [] [⟨.ground,q⟩] [⟨.ground,z⟩] at hm
    have hs := singletonStrict above ⟨.ground,q⟩ ⟨.ground,z⟩ hm
    cases hs with
    | mark a r b hmark hw => cases hmark
  · change p∈[⟨.ground,q⟩] at hp
    have he := List.mem_singleton.mp hp
    subst p
    exact markedKk hw

theorem broadTargetRefutation : MarkedSourceTransitivityCounterexampleTargets.ActualBroadTargetRefutation := by
  intro H
  have habove : Transitive above := fun _ _ _ hab hbc => Nat.lt_trans hbc hab
  exact originalFailure (H Nat arity above habove [] ⟨.ground,s⟩ ⟨.ground,t⟩ ⟨.ground,u⟩ extendedSteps.1 extendedSteps.2.1 extendedSteps.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexampleProof

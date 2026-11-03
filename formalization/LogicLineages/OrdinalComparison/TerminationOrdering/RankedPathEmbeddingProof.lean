module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEqualityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEmbeddingProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication RecursiveComparison RankedTree RankedPathOrder

private theorem fromMarked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Symbol) (args : Fin (arity f) → Tree Symbol arity Gamma)
    (t : Tree Symbol arity Gamma) (h : RecursiveComparison.Weak Symbol arity above Gamma (markedRoot f args) (pack t)) :
    Strict Symbol arity above Gamma (pack (.node f args)) (pack t) := .mark _ _ _ rfl h

private theorem toMarked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Symbol) (args : Fin (arity f) → Tree Symbol arity Gamma)
    (t : Tree Symbol arity Gamma) (h : Strict Symbol arity above Gamma (pack (.node f args)) (pack t)) :
    RecursiveComparison.Weak Symbol arity above Gamma (markedRoot f args) (pack t) := by
  cases h with
  | mark s r t hm hw =>
    have hr : (markedRoot f args).2=r := Option.some.inj hm
    subst r
    exact hw

theorem strict {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Tree Symbol arity Gamma}
    (h : Greater Symbol arity Gamma above s t) :
    Strict Symbol arity above Gamma (pack s) (pack t) := by
  induction h using Greater.rec
    (motive_2 := fun s t _ => RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t))
    (motive_3 := fun ss ts _ => StrictMultiset Symbol arity above Gamma (ss.map pack) (ts.map pack))
    (motive_4 := fun ss ts _ => ReplacementMatch Symbol arity above Gamma (ss.map pack) (ts.map pack))
    with
  | subterm f ss i t hs ihs =>
    apply fromMarked above f ss t
    apply RecursiveComparison.Weak.select (.ranked f)
      (groundArguments (arity f) (fun j => markedSyntax (ss j))) [] .nil []
      (markedSyntax (ss i)) (markedSyntax (ss i)) (markedSyntax t) rfl
    · change pack (ss i)∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun j => markedSyntax (ss j)))++[]
      rw [List.append_nil,RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss]
      exact List.mem_map.mpr ⟨ss i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
    · exact Source.SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma .ground (markedSyntax (ss i))
    · exact ihs
  | precedence f g ss ts hp hall ihall =>
    apply fromMarked above f ss (.node g ts)
    apply RecursiveComparison.Weak.copy (.ranked f) (.ranked g)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) hp
    intro p hm
    change p∈argumentList (types := List.replicate (arity g) Ty.ground)
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) at hm
    rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity g) ts] at hm
    rcases List.mem_map.mp hm with ⟨child,hc,he⟩
    rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
    subst child
    subst p
    exact toMarked above f ss (ts i) (ihall i)
  | multiset f ss ts hm hall ihm ihall =>
    apply fromMarked above f ss (.node f ts)
    apply RecursiveComparison.Weak.stat (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity f) (fun i => markedSyntax (ts i))) rfl
    · change StrictMultiset Symbol arity above Gamma
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ss i))))
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ts i))))
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss,
        RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts]
      exact ihm
    · intro p hp
      change p∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun i => markedSyntax (ts i))) at hp
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts] at hp
      rcases List.mem_map.mp hp with ⟨child,hc,he⟩
      rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
      subst child
      subst p
      exact toMarked above f ss (ts i) (ihall i)
  | equal s t he => exact RankedPathEqualityProof.equality above he
  | greater s t hg ihg => exact RecursiveComparisonProof.strictWeakInclusion Symbol arity above Gamma _ _ ihg
  | replace ss ts kept retained removed inserted hs ht hn hk hr ihr =>
    apply StrictMultiset.replace (ss.map pack) (ts.map pack) (kept.map pack) (retained.map pack)
      (removed.map pack) (inserted.map pack)
    · simpa only [List.map_append] using hs.map pack
    · simpa only [List.map_append] using ht.map pack
    · simpa using hn
    · exact RankedPathEqualityProof.equalityMatch above hk
    · exact ihr
  | nil removed => exact .nil _
  | cons removed s t rest hm hq hr ihq ihr =>
    exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hm,rfl⟩) ihq ihr
theorem weak {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Tree Symbol arity Gamma}
    (h : RankedPathOrder.Weak Symbol arity Gamma above s t) :
    RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t) := by
  induction h using RankedPathOrder.Weak.rec
    (motive_1 := fun s t _ => Strict Symbol arity above Gamma (pack s) (pack t))
    (motive_3 := fun ss ts _ => StrictMultiset Symbol arity above Gamma (ss.map pack) (ts.map pack))
    (motive_4 := fun ss ts _ => ReplacementMatch Symbol arity above Gamma (ss.map pack) (ts.map pack))
    with
  | subterm f ss i t hs ihs =>
    apply fromMarked above f ss t
    apply RecursiveComparison.Weak.select (.ranked f)
      (groundArguments (arity f) (fun j => markedSyntax (ss j))) [] .nil []
      (markedSyntax (ss i)) (markedSyntax (ss i)) (markedSyntax t) rfl
    · change pack (ss i)∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun j => markedSyntax (ss j)))++[]
      rw [List.append_nil,RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss]
      exact List.mem_map.mpr ⟨ss i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
    · exact Source.SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma .ground (markedSyntax (ss i))
    · exact ihs
  | precedence f g ss ts hp hall ihall =>
    apply fromMarked above f ss (.node g ts)
    apply RecursiveComparison.Weak.copy (.ranked f) (.ranked g)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) hp
    intro p hm
    change p∈argumentList (types := List.replicate (arity g) Ty.ground)
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) at hm
    rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity g) ts] at hm
    rcases List.mem_map.mp hm with ⟨child,hc,he⟩
    rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
    subst child
    subst p
    exact toMarked above f ss (ts i) (ihall i)
  | multiset f ss ts hm hall ihm ihall =>
    apply fromMarked above f ss (.node f ts)
    apply RecursiveComparison.Weak.stat (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity f) (fun i => markedSyntax (ts i))) rfl
    · change StrictMultiset Symbol arity above Gamma
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ss i))))
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ts i))))
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss,
        RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts]
      exact ihm
    · intro p hp
      change p∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun i => markedSyntax (ts i))) at hp
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts] at hp
      rcases List.mem_map.mp hp with ⟨child,hc,he⟩
      rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
      subst child
      subst p
      exact toMarked above f ss (ts i) (ihall i)
  | equal s t he => exact RankedPathEqualityProof.equality above he
  | greater s t hg ihg => exact RecursiveComparisonProof.strictWeakInclusion Symbol arity above Gamma _ _ ihg
  | replace ss ts kept retained removed inserted hs ht hn hk hr ihr =>
    apply StrictMultiset.replace (ss.map pack) (ts.map pack) (kept.map pack) (retained.map pack)
      (removed.map pack) (inserted.map pack)
    · simpa only [List.map_append] using hs.map pack
    · simpa only [List.map_append] using ht.map pack
    · simpa using hn
    · exact RankedPathEqualityProof.equalityMatch above hk
    · exact ihr
  | nil removed => exact .nil _
  | cons removed s t rest hm hq hr ihq ihr =>
    exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hm,rfl⟩) ihq ihr
theorem multiset {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Tree Symbol arity Gamma)}
    (h : MultisetGreater Symbol arity Gamma above ss ts) :
    StrictMultiset Symbol arity above Gamma (ss.map pack) (ts.map pack) := by
  induction h using MultisetGreater.rec
    (motive_1 := fun s t _ => Strict Symbol arity above Gamma (pack s) (pack t))
    (motive_2 := fun s t _ => RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t))
    (motive_4 := fun ss ts _ => ReplacementMatch Symbol arity above Gamma (ss.map pack) (ts.map pack))
    with
  | subterm f ss i t hs ihs =>
    apply fromMarked above f ss t
    apply RecursiveComparison.Weak.select (.ranked f)
      (groundArguments (arity f) (fun j => markedSyntax (ss j))) [] .nil []
      (markedSyntax (ss i)) (markedSyntax (ss i)) (markedSyntax t) rfl
    · change pack (ss i)∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun j => markedSyntax (ss j)))++[]
      rw [List.append_nil,RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss]
      exact List.mem_map.mpr ⟨ss i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
    · exact Source.SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma .ground (markedSyntax (ss i))
    · exact ihs
  | precedence f g ss ts hp hall ihall =>
    apply fromMarked above f ss (.node g ts)
    apply RecursiveComparison.Weak.copy (.ranked f) (.ranked g)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) hp
    intro p hm
    change p∈argumentList (types := List.replicate (arity g) Ty.ground)
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) at hm
    rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity g) ts] at hm
    rcases List.mem_map.mp hm with ⟨child,hc,he⟩
    rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
    subst child
    subst p
    exact toMarked above f ss (ts i) (ihall i)
  | multiset f ss ts hm hall ihm ihall =>
    apply fromMarked above f ss (.node f ts)
    apply RecursiveComparison.Weak.stat (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity f) (fun i => markedSyntax (ts i))) rfl
    · change StrictMultiset Symbol arity above Gamma
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ss i))))
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ts i))))
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss,
        RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts]
      exact ihm
    · intro p hp
      change p∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun i => markedSyntax (ts i))) at hp
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts] at hp
      rcases List.mem_map.mp hp with ⟨child,hc,he⟩
      rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
      subst child
      subst p
      exact toMarked above f ss (ts i) (ihall i)
  | equal s t he => exact RankedPathEqualityProof.equality above he
  | greater s t hg ihg => exact RecursiveComparisonProof.strictWeakInclusion Symbol arity above Gamma _ _ ihg
  | replace ss ts kept retained removed inserted hs ht hn hk hr ihr =>
    apply StrictMultiset.replace (ss.map pack) (ts.map pack) (kept.map pack) (retained.map pack)
      (removed.map pack) (inserted.map pack)
    · simpa only [List.map_append] using hs.map pack
    · simpa only [List.map_append] using ht.map pack
    · simpa using hn
    · exact RankedPathEqualityProof.equalityMatch above hk
    · exact ihr
  | nil removed => exact .nil _
  | cons removed s t rest hm hq hr ihq ihr =>
    exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hm,rfl⟩) ihq ihr
theorem replacement {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Tree Symbol arity Gamma)}
    (h : Replacement Symbol arity Gamma above ss ts) :
    ReplacementMatch Symbol arity above Gamma (ss.map pack) (ts.map pack) := by
  induction h using Replacement.rec
    (motive_1 := fun s t _ => Strict Symbol arity above Gamma (pack s) (pack t))
    (motive_2 := fun s t _ => RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t))
    (motive_3 := fun ss ts _ => StrictMultiset Symbol arity above Gamma (ss.map pack) (ts.map pack))
    with
  | subterm f ss i t hs ihs =>
    apply fromMarked above f ss t
    apply RecursiveComparison.Weak.select (.ranked f)
      (groundArguments (arity f) (fun j => markedSyntax (ss j))) [] .nil []
      (markedSyntax (ss i)) (markedSyntax (ss i)) (markedSyntax t) rfl
    · change pack (ss i)∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun j => markedSyntax (ss j)))++[]
      rw [List.append_nil,RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss]
      exact List.mem_map.mpr ⟨ss i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
    · exact Source.SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma .ground (markedSyntax (ss i))
    · exact ihs
  | precedence f g ss ts hp hall ihall =>
    apply fromMarked above f ss (.node g ts)
    apply RecursiveComparison.Weak.copy (.ranked f) (.ranked g)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) hp
    intro p hm
    change p∈argumentList (types := List.replicate (arity g) Ty.ground)
      (groundArguments (arity g) (fun i => markedSyntax (ts i))) at hm
    rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity g) ts] at hm
    rcases List.mem_map.mp hm with ⟨child,hc,he⟩
    rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
    subst child
    subst p
    exact toMarked above f ss (ts i) (ihall i)
  | multiset f ss ts hm hall ihm ihall =>
    apply fromMarked above f ss (.node f ts)
    apply RecursiveComparison.Weak.stat (.ranked f) (.ranked f)
      (groundArguments (arity f) (fun i => markedSyntax (ss i))) [] .nil
      (groundArguments (arity f) (fun i => markedSyntax (ts i))) rfl
    · change StrictMultiset Symbol arity above Gamma
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ss i))))
        (argumentList (types := List.replicate (arity f) Ty.ground) (groundArguments (arity f) (fun i => markedSyntax (ts i))))
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ss,
        RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts]
      exact ihm
    · intro p hp
      change p∈argumentList (types := List.replicate (arity f) Ty.ground)
        (groundArguments (arity f) (fun i => markedSyntax (ts i))) at hp
      rw [RankedTreeProof.literalArgumentList Symbol arity Gamma (arity f) ts] at hp
      rcases List.mem_map.mp hp with ⟨child,hc,he⟩
      rcases List.mem_ofFn.mp hc with ⟨i,hi⟩
      subst child
      subst p
      exact toMarked above f ss (ts i) (ihall i)
  | equal s t he => exact RankedPathEqualityProof.equality above he
  | greater s t hg ihg => exact RecursiveComparisonProof.strictWeakInclusion Symbol arity above Gamma _ _ ihg
  | replace ss ts kept retained removed inserted hs ht hn hk hr ihr =>
    apply StrictMultiset.replace (ss.map pack) (ts.map pack) (kept.map pack) (retained.map pack)
      (removed.map pack) (inserted.map pack)
    · simpa only [List.map_append] using hs.map pack
    · simpa only [List.map_append] using ht.map pack
    · simpa using hn
    · exact RankedPathEqualityProof.equalityMatch above hk
    · exact ihr
  | nil removed => exact .nil _
  | cons removed s t rest hm hq hr ihq ihr =>
    exact .cons _ _ _ _ (List.mem_map.mpr ⟨s,hm,rfl⟩) ihq ihr

theorem jointStrictEmbedding : RankedPathEmbeddingTargets.JointStrictEmbedding := by
  intro Symbol arity Gamma above
  exact ⟨fun _ _ h => strict above h,fun _ _ h => weak above h,
    fun _ _ h => multiset above h,fun _ _ h => replacement above h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathEmbeddingProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseOperationsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseOperationsProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseBindingProof NumberedUniverseOperationsTargets

theorem rootType {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (K : Ty → Prop) (H : Head Symbol → Prop) (q : AuxTerm Symbol arity Gamma tau) (h : Good K H q) : K tau := by
  cases q <;> first | exact h.1 | exact h.1.1

theorem actualArgumentOccurrences : ActualArgumentOccurrences := by
  intro Symbol arity K H Gamma types args
  induction types with
  | nil => cases args; simp [GoodArguments,auxArgumentTypesAllowed,auxArgumentsAllowed,argumentList]
  | cons tau types ih => cases args with
    | cons q rest =>
      constructor
      · intro h p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨h.1.1,h.2.1⟩
        · exact (ih rest).mp ⟨h.1.2,h.2.2⟩ p hp
      · intro h
        have hq := h ⟨tau,q⟩ (by simp [argumentList])
        have hr := (ih rest).mpr (fun p hp => h p (List.mem_cons_of_mem _ hp))
        exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

theorem actualArgumentAppend : ActualArgumentAppend := by
  intro Symbol arity K H Gamma xs ys a b ha hb
  exact appendGood K H a b ha hb

theorem arrowDomain (K : Ty → Prop) (hc : SubtypeClosed K) (sigma tau : Ty) (h : K (.arrow sigma tau)) : K sigma :=
  hc _ h _ (by simp [Ty.subtypes,NumberedFiniteUniverseProof.subtypeSelf])

theorem arrowCodomain (K : Ty → Prop) (hc : SubtypeClosed K) (sigma tau : Ty) (h : K (.arrow sigma tau)) : K tau :=
  hc _ h _ (by simp [Ty.subtypes,NumberedFiniteUniverseProof.subtypeSelf])

theorem applyGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    (hc : SubtypeClosed K) (Gamma types : List Ty) : ∀ (tau : Ty)
    (q : AuxTerm Symbol arity Gamma (arrows types tau)) (args : AuxArguments Symbol arity Gamma types),
    Good K H q → GoodArguments K H args → Good K H (applyArguments q args) := by
  induction types with
  | nil => intro tau q args hq ha; cases args; exact hq
  | cons sigma types ih =>
    intro tau q args hq ha
    cases args with
    | cons a rest =>
      have ht := arrowCodomain K hc sigma (arrows types tau) (rootType K H q hq)
      apply ih tau (.app q a) rest
      · exact ⟨⟨ht,hq.1,ha.1.1⟩,hq.2,ha.2.1⟩
      · exact ⟨ha.1.2,ha.2.2⟩

theorem actualCompleteApplication : ActualCompleteApplication := by
  intro Symbol arity K H hc Gamma types tau q args hq ha
  exact applyGood K H hc Gamma types tau q args hq ha

theorem actualPrimitiveMultiset : ActualPrimitiveMultiset := by
  intro Symbol arity K H Gamma ss ts hm hs q hq
  obtain ⟨kept,removed,inserted,hss,hts,hne,hr⟩ := hm
  rcases List.mem_append.mp (hts.mem_iff.mp hq) with hk | hi
  · exact hs q (hss.mem_iff.mpr (List.mem_append_left _ hk))
  · obtain ⟨s,hsr,hmark⟩ := hr q hi
    have hsg := hs s (hss.mem_iff.mpr (List.mem_append_right _ hsr))
    cases hmark with
    | mk n a b he => exact markGood K H n a b he hsg

theorem arrowArgumentTypes (K : Ty → Prop) (hc : SubtypeClosed K) (types : List Ty) (tau : Ty)
    (h : K (arrows types tau)) : ∀ sigma∈types,K sigma := by
  induction types with
  | nil => intro sigma hs; cases hs
  | cons sigma types ih =>
    intro upsilon hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact arrowDomain K hc upsilon (arrows types tau) h
    · exact ih (arrowCodomain K hc sigma (arrows types tau) h) upsilon hu

theorem actualSelect : ActualSelect := by
  intro Symbol arity K H hc n Gamma f tau base extraTypes extras types selected hm h
  have hb : GoodArguments K H base := ⟨h.1.2.1,h.2.2.1⟩
  have he : GoodArguments K H extras := ⟨h.1.2.2,h.2.2.2⟩
  have hs : Good K H selected := by
    rcases List.mem_append.mp hm with hm | hm
    · exact (actualArgumentOccurrences Symbol arity K H Gamma _ base).mp hb _ hm
    · exact (actualArgumentOccurrences Symbol arity K H Gamma _ extras).mp he _ hm
  have ht := arrowArgumentTypes K hc types tau (rootType K H selected hs)
  have hself := actualSelfArguments Symbol arity K H n Gamma f base extraTypes extras types h.2.1 hb he ht
  exact applyGood K H hc Gamma types tau selected _ hs hself

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseOperationsProof

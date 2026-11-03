module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowListCasesTargets

@[expose] public section
/-! Proven CONSTRUCTOR CASES with explicit induction hypotheses, not an
unconditional simulation theorem. The final actual mutual induction is still
required. No certificate is installed as an axiom or hidden class field.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowListCasesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowTraces NumberedWindowOccurrenceTargets NumberedWindowListCasesTargets

theorem weakRaise {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n m : Nat} {s t : OriginalPacked Symbol arity Gamma} (hnm : n≤m)
    (h : WeakAt symbols S above n s t) : WeakAt symbols S above m s t := by
  intro Q hQ hgood ht
  exact h Q (NumberedRewriteSyntaxProof.budgetLowering Symbol arity m n hnm Gamma s.1 s.2 Q hQ) hgood ht

theorem strictRaise {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n m : Nat} {s t : OriginalPacked Symbol arity Gamma} (hnm : n≤m)
    (h : StrictAt symbols S above n s t) : StrictAt symbols S above m s t := by
  intro Q hQ hgood ht
  exact h Q (NumberedRewriteSyntaxProof.budgetLowering Symbol arity m n hnm Gamma s.1 s.2 Q hQ) hgood ht

theorem representedMember {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {n : Nat}
    {qs : List (OriginalPacked Symbol arity Gamma)} {values : List (Packed Symbol arity Gamma)}
    (h : ListRep n qs values) : ∀ q∈qs,∃ Q∈values,PackedRep n q Q := by
  induction h with
  | nil => intro q hq; cases hq
  | @cons q Q qs values hq hr ih =>
    intro r hm
    rcases List.mem_cons.mp hm with he | ht
    · subst r; exact ⟨Q,List.mem_cons_self ..,hq⟩
    · obtain ⟨R,hR,hrel⟩ := ih r ht
      exact ⟨R,List.mem_cons_of_mem _ hR,hrel⟩

theorem matchNil : ActualMatchNil := by
  intro Symbol arity symbols S above Gamma
  refine ⟨0,?_⟩
  intro values h hgood ht
  cases h
  exact .nil

theorem matchCons : ActualMatchCons := by
  intro Symbol arity symbols S above Gamma s t ss ts hs hr
  obtain ⟨n,hn⟩ := hs
  obtain ⟨m,hm⟩ := hr
  refine ⟨max n m,?_⟩
  intro values h hgood ht
  cases h with
  | cons hq hrest =>
    obtain ⟨Q,rfl,hQ⟩ := hq
    exact .cons (weakRaise (Nat.le_max_left n m) hn Q hQ (hgood _ (List.mem_cons_self ..)) (ht _ (List.mem_cons_self ..)))
      (hm _ (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) m
        (Nat.le_max_right n m) Gamma ss _ hrest)
        (fun q hq => hgood q (List.mem_cons_of_mem _ hq))
        (fun t htmem => ht t (List.mem_cons_of_mem _ htmem)))

theorem strictMarkCase : ActualStrictMark := by
  intro Symbol arity symbols S above Gamma tau s r t hm h
  obtain ⟨n,hn⟩ := h
  refine ⟨n+1,?_⟩
  intro Q hQ hgood ht
  obtain ⟨R,he,hR⟩ := NumberedRepresentationRigidityProof.finiteMarkWitness Symbol arity n Gamma tau s r hm Q hQ
  have hgR := NumberedUniverseBindingProof.actualFiniteMark Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) n Gamma tau Q R he hgood
  exact ⟨n,R,he,hn R hR hgR ht⟩

theorem replacementNil : ActualReplacementNil := by
  intro Symbol arity symbols S above Gamma removed
  refine ⟨0,?_⟩
  intro values h hgood ht
  refine ⟨[],?_,.nil⟩
  intro R hR
  cases hR

theorem replacementCons : ActualReplacementCons := by
  intro Symbol arity symbols S above Gamma removed s t rest hs hstrict hrest
  obtain ⟨n,hn⟩ := hstrict
  obtain ⟨m,hm⟩ := hrest
  refine ⟨max n m,?_⟩
  intro values hvalues hgood htarget
  obtain ⟨Q,hQmem,hQ⟩ := representedMember hvalues s hs
  obtain ⟨A,rfl,hA⟩ := hQ
  obtain ⟨k,R,hmark,nt,htrace⟩ := strictRaise (Nat.le_max_left n m) hn A hA (hgood _ hQmem) (htarget _ (List.mem_cons_self ..))
  obtain ⟨marked,hmarks,htraces⟩ := hm values
    (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) m (Nat.le_max_right n m) Gamma removed values hvalues) hgood (fun t ht => htarget t (List.mem_cons_of_mem _ ht))
  refine ⟨⟨s.1,R⟩::marked,?_,.cons ⟨nt,htrace⟩ htraces⟩
  intro P hP
  rcases List.mem_cons.mp hP with he | ht
  · subst P; exact ⟨⟨s.1,A⟩,hQmem,.mk k A R hmark⟩
  · exact hmarks P ht

theorem flipRelation {alpha beta : Type} {R : alpha → beta → Prop} {xs : List alpha} {ys : List beta}
    (h : List.Forall₂ R xs ys) : List.Forall₂ (fun y x => R x y) ys xs := by
  induction h with
  | nil => exact .nil
  | cons h hr ih => exact .cons h ih

theorem appendRelation {alpha beta : Type} {R : alpha → beta → Prop} {xs xs' : List alpha} {ys ys' : List beta}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ R xs' ys') : List.Forall₂ R (xs++xs') (ys++ys') := by
  induction h with
  | nil => exact h'
  | cons h hr ih => exact .cons h ih

theorem multisetReplace : ActualMultisetReplace := by
  intro Symbol arity symbols S above Gamma ss ts kept retained removed inserted hp ht hremoved hmatch hreplace
  obtain ⟨n,hn⟩ := hmatch
  obtain ⟨m,hm⟩ := hreplace
  refine ⟨max n m,?_⟩
  intro values hvalues hgood htarget
  obtain ⟨reordered,horder,hreordered⟩ := NumberedOccurrenceTransportProof.permutationTransport Symbol arity (max n m) Gamma ss (kept++removed) values hp hvalues
  obtain ⟨keptValues,removedValues,he,hkept,hremovedValues⟩ := NumberedOccurrenceTransportProof.splitTransport Symbol arity (max n m) Gamma kept removed reordered hreordered
  have horder' : values.Perm (keptValues++removedValues) := by rw [←he]; exact horder
  have hnonempty : removedValues≠[] := by
    intro hempty
    subst removedValues
    cases hremovedValues
    exact hremoved rfl
  have hkeptGood : GoodList symbols S keptValues := by
    intro q hq
    exact hgood q (horder'.mem_iff.mpr (List.mem_append_left _ hq))
  have hremovedGood : GoodList symbols S removedValues := by
    intro q hq
    exact hgood q (horder'.mem_iff.mpr (List.mem_append_right _ hq))
  have hretainedGood : OriginalGoodList symbols S retained := by
    intro q hq
    exact htarget q (ht.mem_iff.mpr (List.mem_append_left _ hq))
  have hinsertedGood : OriginalGoodList symbols S inserted := by
    intro q hq
    exact htarget q (ht.mem_iff.mpr (List.mem_append_right _ hq))
  have hkeepTrace := hn keptValues (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) n
    (Nat.le_max_left n m) Gamma kept keptValues hkept) hkeptGood hretainedGood
  obtain ⟨marked,hmark,hmarkedTrace⟩ := hm removedValues (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) m
    (Nat.le_max_right n m) Gamma removed removedValues hremovedValues) hremovedGood hinsertedGood
  have hcombined : PointwiseWindowTrace symbols S above (keptValues++marked) (canonicalList 0 (retained++inserted)) := by
    simpa only [PointwiseWindowTrace,canonicalList,List.map_append] using appendRelation hkeepTrace hmarkedTrace
  have hcanonical := (ht.map (canonicalPacked 0)).symm
  obtain ⟨middle,hmiddle,hflipped⟩ := NumberedOccurrenceTransportProof.permuteRelation
    (fun q r => ∃ n,WindowTrace Symbol arity symbols S above Gamma n r q) hcanonical (keptValues++marked) (flipRelation hcombined)
  refine ⟨middle,⟨keptValues,removedValues,marked,horder',hmiddle.symm,hnonempty,hmark⟩,?_⟩
  exact flipRelation hflipped

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowListCasesProof

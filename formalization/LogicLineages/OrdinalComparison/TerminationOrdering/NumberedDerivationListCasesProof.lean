module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationCertificatesDefinitions

@[expose] public section
/-! Proven CONSTRUCTOR CASES with explicit induction hypotheses, not an
unconditional simulation theorem. The final actual mutual induction is still
required. No certificate is installed as an axiom or hidden class field.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationListCasesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedDerivationCertificates

theorem weakRaise {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n m : Nat} {s t : OriginalPacked Symbol arity Gamma} (hnm : n≤m)
    (h : WeakAt above n s t) : WeakAt above m s t := by
  intro Q hQ
  exact h Q (NumberedRewriteSyntaxProof.budgetLowering Symbol arity m n hnm Gamma s.1 s.2 Q hQ)

theorem strictRaise {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n m : Nat} {s t : OriginalPacked Symbol arity Gamma} (hnm : n≤m)
    (h : StrictAt above n s t) : StrictAt above m s t := by
  intro Q hQ
  exact h Q (NumberedRewriteSyntaxProof.budgetLowering Symbol arity m n hnm Gamma s.1 s.2 Q hQ)

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

theorem matchNil {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) : MatchCertificate above ([] : List (OriginalPacked Symbol arity Gamma)) [] := by
  refine ⟨0,?_⟩
  intro values h
  cases h
  exact .nil

theorem matchCons {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (s t : OriginalPacked Symbol arity Gamma) (ss ts : List (OriginalPacked Symbol arity Gamma))
    (hs : WeakCertificate above s t) (hr : MatchCertificate above ss ts) : MatchCertificate above (s::ss) (t::ts) := by
  obtain ⟨n,hn⟩ := hs
  obtain ⟨m,hm⟩ := hr
  refine ⟨max n m,?_⟩
  intro values h
  cases h with
  | cons hq hrest =>
    obtain ⟨Q,rfl,hQ⟩ := hq
    exact .cons (weakRaise (Nat.le_max_left n m) hn Q hQ)
      (hm _ (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) m
        (Nat.le_max_right n m) Gamma ss _ hrest))

theorem strictMarkCase {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {tau : Ty} (s r t : MarkedTerm Symbol arity Gamma tau)
    (hm : RecursiveComparison.strictMark s=some r) (h : WeakCertificate above ⟨tau,r⟩ ⟨tau,t⟩) :
    StrictCertificate above ⟨tau,s⟩ ⟨tau,t⟩ := by
  obtain ⟨n,hn⟩ := h
  refine ⟨n+1,?_⟩
  intro Q hQ
  obtain ⟨R,he,hR⟩ := NumberedRepresentationRigidityProof.finiteMarkWitness Symbol arity n Gamma tau s r hm Q hQ
  exact ⟨n,R,he,hn R hR⟩

theorem replacementNil {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (removed : List (OriginalPacked Symbol arity Gamma)) : ReplacementCertificate above removed [] := by
  refine ⟨0,?_⟩
  intro values h
  refine ⟨[],?_,.nil⟩
  intro R hR
  cases hR

theorem replacementCons {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (removed : List (OriginalPacked Symbol arity Gamma)) (s t : OriginalPacked Symbol arity Gamma)
    (rest : List (OriginalPacked Symbol arity Gamma)) (hs : s∈removed)
    (hstrict : StrictCertificate above s t) (hrest : ReplacementCertificate above removed rest) :
    ReplacementCertificate above removed (t::rest) := by
  obtain ⟨n,hn⟩ := hstrict
  obtain ⟨m,hm⟩ := hrest
  refine ⟨max n m,?_⟩
  intro values hvalues
  obtain ⟨Q,hQmem,hQ⟩ := representedMember hvalues s hs
  obtain ⟨A,rfl,hA⟩ := hQ
  obtain ⟨k,R,hmark,nt,htrace⟩ := strictRaise (Nat.le_max_left n m) hn A hA
  obtain ⟨marked,hmarks,htraces⟩ := hm values
    (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) m (Nat.le_max_right n m) Gamma removed values hvalues)
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

theorem multisetReplace {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} (ss ts kept retained removed inserted : List (OriginalPacked Symbol arity Gamma))
    (hp : ss.Perm (kept++removed)) (ht : ts.Perm (retained++inserted)) (hremoved : removed≠[])
    (hmatch : MatchCertificate above kept retained) (hreplace : ReplacementCertificate above removed inserted) :
    MultiCertificate above ss ts := by
  obtain ⟨n,hn⟩ := hmatch
  obtain ⟨m,hm⟩ := hreplace
  refine ⟨max n m,?_⟩
  intro values hvalues
  obtain ⟨reordered,horder,hreordered⟩ := NumberedOccurrenceTransportProof.permutationTransport Symbol arity (max n m) Gamma ss (kept++removed) values hp hvalues
  obtain ⟨keptValues,removedValues,he,hkept,hremovedValues⟩ := NumberedOccurrenceTransportProof.splitTransport Symbol arity (max n m) Gamma kept removed reordered hreordered
  have horder' : values.Perm (keptValues++removedValues) := by rw [←he]; exact horder
  have hnonempty : removedValues≠[] := by
    intro hempty
    subst removedValues
    cases hremovedValues
    exact hremoved rfl
  have hkeepTrace := hn keptValues (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) n
    (Nat.le_max_left n m) Gamma kept keptValues hkept)
  obtain ⟨marked,hmark,hmarkedTrace⟩ := hm removedValues (NumberedOccurrenceTransportProof.listBudgetLowering Symbol arity (max n m) m
    (Nat.le_max_right n m) Gamma removed removedValues hremovedValues)
  have hcombined : PointwiseTrace above (keptValues++marked) (canonicalList 0 (retained++inserted)) := by
    simpa only [PointwiseTrace,canonicalList,List.map_append] using appendRelation hkeepTrace hmarkedTrace
  have hcanonical := (ht.map (canonicalPacked 0)).symm
  obtain ⟨middle,hmiddle,hflipped⟩ := NumberedOccurrenceTransportProof.permuteRelation
    (fun q r => ∃ n,Trace Symbol arity above Gamma n r q) hcanonical (keptValues++marked) (flipRelation hcombined)
  refine ⟨middle,⟨keptValues,removedValues,marked,horder',hmiddle.symm,hnonempty,hmark⟩,?_⟩
  exact flipRelation hflipped

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationListCasesProof

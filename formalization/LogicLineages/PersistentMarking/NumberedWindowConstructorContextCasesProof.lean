import LogicLineages.PersistentMarking.NumberedWindowConstructorInductionProof
import LogicLineages.PersistentMarking.NumberedWindowConstructorRawArgumentChecks
import LogicLineages.PersistentMarking.NumberedWindowConstructorStatAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentComputabilityChecks

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorContextCasesProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowArithmeticLeastClass NumberedWindowRules
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorArgumentAddressChecks
open NumberedWindowConstructorOrderTargets NumberedWindowConstructorComputabilityTargets
open NumberedWindowConstructorRepresentationProof NumberedWindowConstructorRawArgumentChecks
open NumberedWindowConstructorArgumentComputabilityChecks NumberedWindowSimulationData
open NumberedWindowArithmeticDirectMultisetTargets

theorem sameHead {S K f} (hf : HeadInWindow S K f) : Spine.Equivalent S f f := by
  obtain ⟨i,hi⟩ := hf.1
  exact ⟨i,hi,hi⟩

theorem bottom {S K Γ hk τ} (hw : InWindow S K (finiteC Γ) τ (.bottom τ)) :
    ComputableArgument S K Γ hk (.bottom τ) :=
  ⟨hw, NumberedWindowExternalTypeFactsChecks.exact_BottomComputability S K Γ τ hk _
    ⟨⟨.bottom τ,hw⟩,rfl,rfl⟩⟩

theorem emptyMembers {S K Γ hk} : Members S K Γ hk .nil := fun _ h => nomatch h

private theorem context {S K Γ hk xs ys} {b : List Nat} (sb : Slots S K Γ xs b)
    (m : Members S K Γ hk xs) (w : ∀ q ∈ ys.toList, InWindow S K (finiteC Γ) q.type q)
    (h : RawArgsStep S K xs ys) :
    ∃ c, Slots S K Γ ys c ∧ AddressDirect S K b c ∧ Members S K Γ hk ys := by
  have mc := exact_RawArgsStepComputableArguments S K Γ hk xs ys m (fun x hx => (w x hx).1) h
  obtain ⟨c,sc,_⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk ys mc
  exact ⟨c,sc,(exact_RawArgumentAddressDescent S K Γ xs ys b c hk
    (fun x hx => (m x hx).choose) w h sb sc).1,mc⟩

theorem base {S K Γ hk} (o p : Owner) {b e}
    (sb : Slots S K Γ o.base b) (se : Slots S K Γ o.extras e)
    (mb : Members S K Γ hk o.base) (me : Members S K Γ hk o.extras)
    (ih : Hypothesis S K Γ hk (o.measure b e))
    (hp : InWindow S K (finiteC Γ) p.term.type p.term)
    (head : o.head = p.head) (extra : o.extras = p.extras)
    (h : RawArgsStep S K o.base p.base) : ComputableArgument S K Γ hk p.term := by
  obtain ⟨hf,hw,_⟩ := ownerParts p hp
  obtain ⟨c,sc,d,mc⟩ := context sb mb hw h
  have eq : Spine.Equivalent S o.head p.head := by rw [head]; exact sameHead hf
  exact ih p c e sc (extra ▸ se) (Or.inr ⟨eq,Or.inl d⟩) hp mc (extra ▸ me)

theorem extras {S K Γ hk f τ k bs es ys} {b e}
    (sb : Slots S K Γ bs b) (se : Slots S K Γ es e)
    (mb : Members S K Γ hk bs) (me : Members S K Γ hk es)
    (ih : Hypothesis S K Γ hk ((Owner.numbered f τ k bs es).measure b e))
    (hp : InWindow S K (finiteC Γ) τ (.numbered f τ k bs ys))
    (h : RawArgsStep S K es ys) : ComputableArgument S K Γ hk (.numbered f τ k bs ys) := by
  let p := Owner.numbered f τ k bs ys
  obtain ⟨hf,_,hw⟩ := ownerParts p hp
  obtain ⟨c,sc,d,mc⟩ := context se me hw h
  exact ih p b c sb sc (Or.inr ⟨sameHead hf, Or.inr ⟨List.Perm.refl _,Or.inr ⟨rfl,d⟩⟩⟩) hp mb mc

theorem stat {S K Γ hk f g k bs es ys} {b e}
    (sb : Slots S K Γ bs b) (mb : Members S K Γ hk bs)
    (ih : Hypothesis S K Γ hk ((Owner.numbered f g.result (k+1) bs es).measure b e))
    (hp : InWindow S K (finiteC Γ) g.result (.ordinary g ys)) (eq : Spine.Equivalent S f g)
    (h : PrimitiveReplacement bs ys) : ComputableArgument S K Γ hk (.ordinary g ys) := by
  obtain ⟨c,sc,desc⟩ := NumberedWindowConstructorStatAddressChecks.exact_PrimitiveReplacementAddressDescent
    S K Γ bs ys b hk (fun q hq => (mb q hq).choose) h sb
  exact ih (.ordinary g ys) c [] sc rfl (Or.inr ⟨eq,Or.inl desc⟩) hp
    (exact_PrimitiveReplacementComputableArguments S K Γ hk bs ys mb h) emptyMembers

end LogicLineages.PersistentMarking.NumberedWindowConstructorContextCasesProof

module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorComputabilityTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorHeadProfileChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConstructorOrderChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorRepresentationProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowArithmeticLeastClass NumberedWindowRules
open NumberedWindowConstructorArgumentAddresses NumberedWindowConstructorOrderTargets
open NumberedWindowConstructorComputabilityTargets NumberedWindowConstructorHeadProfileTargets
open NumberedWindowConstructorHeadProfileChecks NumberedWindowConstructorArgumentAddressChecks
open NumberedWindowPreservationGuardProof NumberedWindowNumberedDomainProof
open NumberedWindowArithmeticDirectMultisetTargets NumberedWindowExternalIDOperators
open NumberedWindowArithmeticFields

def Frame (S : Spine.Signature) (K Γ : List Ty) (o : Owner) : HeadProfile :=
  ⟨o.term.type, Spine.classRank S o.head, o.label,
    Quotient.mk addressSetoid (o.base.toList.map (slot S K Γ)),o.extras.toList.map (slot S K Γ)⟩

theorem framed (S K Γ) (o : Owner) : headProfile S K Γ o.term = some (Frame S K Γ o) := by
  cases o <;> rfl

theorem represented {S K Γ q} {fr : HeadProfile} (h : headProfile S K Γ q = some fr) :
    ∃ o : Owner, o.term = q := by
  cases q <;> try cases h
  · exact ⟨.ordinary _ _,rfl⟩
  · exact ⟨.numbered _ _ _ _ _,rfl⟩

private theorem extrasMembers {S K C xs} (t : ExtrasTyped C xs) (g : ArgsGuard S K xs) :
    ∀ q ∈ xs.toList, InWindow S K C q.type q := by
  cases xs with
  | nil => intro q m; cases m
  | cons q xs =>
    cases t with
    | cons hq ht =>
      obtain ⟨hqg,htg⟩ := consParts g
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact annotated ⟨hq,hqg⟩
      · exact extrasMembers ht htg r hr
termination_by sizeOf xs

theorem ownerParts {S K Γ} (o : Owner) (h : InWindow S K (finiteC Γ) o.term.type o.term) :
    HeadInWindow S K o.head ∧
    (∀ q ∈ o.base.toList, InWindow S K (finiteC Γ) q.type q) ∧
    (∀ q ∈ o.extras.toList, InWindow S K (finiteC Γ) q.type q) := by
  cases o with
  | ordinary f bs =>
    obtain ⟨tb,hf,gb⟩ := ordinaryParts h
    exact ⟨hf,extrasMembers (toExtras tb) gb, fun _ h => nomatch h⟩
  | numbered f τ k bs es =>
    obtain ⟨tb,te,hf,gb,ge⟩ := parts h
    exact ⟨hf,extrasMembers (toExtras tb) gb,extrasMembers te ge⟩

private theorem transportMembers {S K Γ hk xs ys}
    (perm : (xs.toList.map (slot S K Γ)).Perm (ys.toList.map (slot S K Γ)))
    (before : Members S K Γ hk xs) (hw : ∀ r ∈ ys.toList, InWindow S K (finiteC Γ) r.type r) :
    Members S K Γ hk ys := by
  intro r hr
  obtain ⟨q,hq,e⟩ := List.mem_map.mp (perm.mem_iff.mpr (List.mem_map.mpr ⟨r,hr,rfl⟩))
  have hc := before q hq
  exact (exact_SameSlotComputable S K Γ hk q r hc.choose (hw r hr) e).mp hc

theorem members {S K Γ hk} {o p : Owner} (e : Frame S K Γ o = Frame S K Γ p)
    (hw : InWindow S K (finiteC Γ) p.term.type p.term)
    (mb : Members S K Γ hk o.base) (me : Members S K Γ hk o.extras) :
    Members S K Γ hk p.base ∧ Members S K Γ hk p.extras := by
  obtain ⟨_,hb,he⟩ := ownerParts p hw
  have eq : o.extras.toList.map (slot S K Γ) = p.extras.toList.map (slot S K Γ) := congrArg HeadProfile.extras e
  exact ⟨transportMembers ((exact_AddressBagExact _ _).mp (congrArg HeadProfile.base e)) mb hb,
    transportMembers (eq ▸ List.Perm.refl _) me he⟩

theorem admitted {S K Γ hk} (o : Owner) {bs es}
    (sb : Slots S K Γ o.base bs) (se : Slots S K Γ o.extras es)
    (hw : InWindow S K (finiteC Γ) o.term.type o.term)
    (mb : Members S K Γ hk o.base) (me : Members S K Γ hk o.extras) :
    AdmittedMeasure S K (o.measure bs es) := by
  obtain ⟨b,hb,_,jb⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk o.base mb
  obtain ⟨e,he,_,je⟩ := exact_ComputableArgumentsGiveMultiset S K Γ hk o.extras me
  have inject : ∀ u v : List Nat, u.map some = v.map some → u = v := by
    intro u v h
    simpa [List.map_map,Function.comp_def] using congrArg (List.map (fun x : Option Nat => x.getD 0)) h
  obtain rfl := inject b bs (hb.symm.trans sb)
  obtain rfl := inject e es (he.symm.trans se)
  exact ⟨(ownerParts o hw).1,jb,je⟩

theorem earlier {S K Γ} {o p : Owner} (e : Frame S K Γ o = Frame S K Γ p)
    {b d c f} (bo : Slots S K Γ o.base b) (eo : Slots S K Γ o.extras d)
    (bp : Slots S K Γ p.base c) (ep : Slots S K Γ p.extras f) {m}
    (h : Earlier S K m (p.measure c f)) : Earlier S K m (o.measure b d) := by
  have rank : Spine.classRank S o.head = Spine.classRank S p.head := congrArg HeadProfile.rank e
  have label : o.label = p.label := congrArg HeadProfile.label e
  have base := (exact_AddressBagExact _ _).mp (congrArg HeadProfile.base e)
  change (o.base.toList.map _).Perm (p.base.toList.map _) at base
  rw [show o.base.toList.map _ = b.map some from bo, show p.base.toList.map _ = c.map some from bp] at base
  have perm : b.Perm c := by simpa [List.map_map,Function.comp_def] using base.map (fun x : Option Nat => x.getD 0)
  have ex : d.map some = f.map some := eo.symm.trans ((congrArg HeadProfile.extras e).trans ep)
  have eq : d = f := by simpa [List.map_map,Function.comp_def] using congrArg (List.map (fun x : Option Nat => x.getD 0)) ex
  rcases h with ⟨a,z,ha,hz,lt⟩ | ⟨⟨a,ha,hz⟩,rest⟩
  · exact Or.inl ⟨a,z,rank.trans ha,hz,lt⟩
  · refine Or.inr ⟨⟨a,rank.trans ha,hz⟩,?_⟩
    rcases rest with direct | ⟨pbase,tail⟩
    · exact Or.inl ((NumberedWindowArithmeticDirectMultisetDomain.permutations S K c b m.base m.base perm.symm (List.Perm.refl _)).mp direct)
    · refine Or.inr ⟨perm.trans pbase,?_⟩
      change LabelBelow m.label o.label ∨ (o.label = m.label ∧ AddressDirect S K d m.extras)
      rw [label,eq]
      exact tail

end LogicLineages.PersistentMarking.NumberedWindowConstructorRepresentationProof

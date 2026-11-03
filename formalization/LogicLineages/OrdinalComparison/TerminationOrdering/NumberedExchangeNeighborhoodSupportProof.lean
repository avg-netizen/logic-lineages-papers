module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedPrimaryExchange NumberedExchangeNeighborhood

theorem listRoundTrip {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : argumentsFromList types (argumentList args)=some args := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest => simp [argumentList,argumentsFromList,ih rest]

theorem listSound {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} (types : List Ty)
    (values : List (Packed Symbol arity Gamma)) (args : AuxArguments Symbol arity Gamma types)
    (h : argumentsFromList types values=some args) : argumentList args=values := by
  induction types generalizing values with
  | nil => cases values with
    | nil => cases h; rfl
    | cons => simp [argumentsFromList] at h
  | cons sigma types ih => cases values with
    | nil => simp [argumentsFromList] at h
    | cons v values =>
      obtain ⟨tau,v⟩ := v
      simp only [argumentsFromList] at h
      split at h
      next he =>
        cases he
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨rest,hr,ha⟩ := h
        cases ha
        exact congrArg (List.cons ⟨sigma,v⟩) (ih values rest hr)
      next => contradiction

theorem typedListReconstruction : NumberedExchangeNeighborhoodTargets.ActualTypedListReconstruction := by
  intro Symbol arity Gamma types values args
  exact ⟨listSound types values args,fun h => h ▸ listRoundTrip args⟩

theorem packedCast {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (h : sigma=tau) (q : AuxTerm Symbol arity Gamma sigma) :
    (⟨tau,h ▸ q⟩ : Packed Symbol arity Gamma)=⟨sigma,q⟩ := by cases h; rfl

theorem ordinarySound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (r : AuxTerm Symbol arity Gamma (headResult f)) (h : r∈ordinaryNeighbors symbols S f base) :
    Exchange Symbol arity symbols S Gamma ⟨_,.ordinary f base⟩ ⟨_,r⟩ := by
  simp only [ordinaryNeighbors] at h
  split at h
  next hf =>
    obtain ⟨g,hg,hr⟩ := List.mem_flatMap.mp h
    split at hr
    next he =>
      split at hr
      next ht =>
        obtain ⟨values,hv,hr⟩ := List.mem_filterMap.mp hr
        obtain ⟨target,ha,heq⟩ := Option.map_eq_some_iff.mp hr
        have hargs := listSound _ values target ha
        have hp := (List.mem_permutations.mp hv).symm
        rw [← hargs] at hp
        have hstep := Exchange.ordinary f g base target hf
          ((NumberedFiniteUniverseProof.headWindow Symbol inferInstance arity symbols S hc g).mp hg) he ht.symm hp
        have hpack : (⟨headResult f,r⟩ : Packed Symbol arity Gamma)=⟨headResult g,AuxTerm.ordinary g target⟩ :=
          (congrArg (fun a : AuxTerm Symbol arity Gamma (headResult f) => (⟨headResult f,a⟩ : Packed Symbol arity Gamma)) heq).symm.trans
            (packedCast ht (AuxTerm.ordinary g target))
        rw [hpack]
        exact hstep
      next => simp at hr
    next => simp at hr
  next => simp at h

theorem numberedSound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (k : Nat) (f : Head Symbol) (tau : Ty) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types)
    (r : AuxTerm Symbol arity Gamma tau) (h : r∈numberedNeighbors symbols S k f tau base types extras) :
    Exchange Symbol arity symbols S Gamma ⟨_,.numbered k f tau base types extras⟩ ⟨_,r⟩ := by
  simp only [numberedNeighbors] at h
  split at h
  next hf =>
    obtain ⟨g,hg,hr⟩ := List.mem_flatMap.mp h
    split at hr
    next he =>
      obtain ⟨values,hv,hr⟩ := List.mem_filterMap.mp hr
      obtain ⟨target,ha,heq⟩ := Option.map_eq_some_iff.mp hr
      have hargs := listSound _ values target ha
      have hp := (List.mem_permutations.mp hv).symm
      rw [← hargs] at hp
      cases heq
      exact .numbered k f g tau base target types extras hf
        ((NumberedFiniteUniverseProof.headWindow Symbol inferInstance arity symbols S hc g).mp hg) he hp
    next => simp at hr
  next => simp at h

theorem ordinaryComplete {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (f g : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (target : AuxArguments Symbol arity Gamma (headArguments arity g))
    (hf : HeadInWindow arity symbols S f) (hg : HeadInWindow arity symbols S g)
    (he : RecursiveComparison.headEquivalent f g) (ht : headResult f=headResult g)
    (hp : (argumentList base).Perm (argumentList target)) :
    ∃ r,r∈ordinaryNeighbors symbols S f base ∧ (⟨headResult f,r⟩ : Packed Symbol arity Gamma)=⟨headResult g,.ordinary g target⟩ := by
  refine ⟨ht.symm ▸ AuxTerm.ordinary g target,?_,?_⟩
  · simp only [ordinaryNeighbors,if_pos hf]
    apply List.mem_flatMap.mpr
    refine ⟨g,(NumberedFiniteUniverseProof.headWindow Symbol inferInstance arity symbols S hc g).mpr hg,?_⟩
    simp only [if_pos he,dif_pos ht.symm]
    apply List.mem_filterMap.mpr
    exact ⟨argumentList target,List.mem_permutations.mpr hp.symm,by rw [listRoundTrip]; rfl⟩
  · exact packedCast ht.symm (AuxTerm.ordinary g target)

theorem numberedComplete {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (hc : SubtypeClosed (fun tau => tau∈S))
    (k : Nat) (f g : Head Symbol) (tau : Ty) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (target : AuxArguments Symbol arity Gamma (headArguments arity g)) (types : List Ty) (extras : AuxArguments Symbol arity Gamma types)
    (hf : HeadInWindow arity symbols S f) (hg : HeadInWindow arity symbols S g)
    (he : RecursiveComparison.headEquivalent f g) (hp : (argumentList base).Perm (argumentList target)) :
    AuxTerm.numbered k g tau target types extras∈numberedNeighbors symbols S k f tau base types extras := by
  simp only [numberedNeighbors,if_pos hf]
  apply List.mem_flatMap.mpr
  refine ⟨g,(NumberedFiniteUniverseProof.headWindow Symbol inferInstance arity symbols S hc g).mpr hg,?_⟩
  simp only [if_pos he]
  apply List.mem_filterMap.mpr
  exact ⟨argumentList target,List.mem_permutations.mpr hp.symm,by rw [listRoundTrip]; rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodSupportProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalSpineActions ActualValueLogicalRelation RecursiveComparison ConstructorInputLogicalRelation

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem packedDownward : ConstructorInputLogicalRelationTargets.PackedDownward := by
  intro Symbol inst arity I above P a b q hab hr
  rcases a with ⟨α,a⟩
  rcases b with ⟨β,b⟩
  have ht : α=β := TypedExtraDownsetsProof.packedType hab
  cases ht
  rcases hr with ⟨t,rfl,ht⟩
  exact ⟨t,rfl,ActualValueLogicalRelationProof.downward above α.val P a b t ((TypedExtraDownsetsProof.packedSame α a b).mp hab) ht⟩

theorem argumentAtMember {Γ : List Ty} {types : List Ty} (args : Arguments Symbol arity Γ types) (i : Fin types.length) :
    (⟨types.get i,argumentAt args i⟩ : RecursiveComparison.Packed Symbol arity Γ) ∈ argumentList args := by
  induction types with
  | nil => exact Fin.elim0 i
  | cons τ rest ih =>
    cases args with
    | cons a as =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih as j)

theorem listAppend {Γ : List Ty} {xs ys : List Ty} (a : Arguments Symbol arity Γ xs) (b : Arguments Symbol arity Γ ys) :
    argumentList (appendArguments a b)=argumentList a++argumentList b := by
  induction xs with
  | nil => cases a; rfl
  | cons τ xs ih => cases a with | cons a as => exact congrArg (List.cons ⟨τ,a⟩) (ih as)

theorem argumentAtRename {Γ Δ : List Ty} {types : List Ty} (args : Arguments Symbol arity Γ types)
    (r : Renaming Γ Δ) (i : Fin types.length) : argumentAt (renameArguments args r) i=renameTerm (argumentAt args i) r := by
  induction types with
  | nil => exact Fin.elim0 i
  | cons τ rest ih =>
    cases args with
    | cons a as =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih as j

theorem inputAppend : ConstructorInputLogicalRelationTargets.InputAppend := by
  intro Symbol inst arity I above f P a base types extras more ht values args ha hv
  constructor
  · exact ha.1
  · intro p hp
    rcases (TypedExtraAppendProof.membershipCalibration Symbol inst arity I P a.2 (packArguments more ht values) p).mp hp with hold | hnew
    · obtain ⟨q,hq,hr⟩ := ha.2 p hold
      exact ⟨q,by rw [listAppend]; exact List.mem_append_left _ hq,hr⟩
    · obtain ⟨b,hb,hpb⟩ := hnew
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      refine ⟨⟨more.get i,argumentAt args i⟩,?_,?_⟩
      · rw [listAppend]
        exact List.mem_append_right _ (argumentAtMember args i)
      · exact packedDownward Symbol inst arity I above P p _ _ hpb ⟨argumentAt args i,rfl,hv i⟩

theorem packedWeakenRelated (above : Symbol → Symbol → Prop) {P Q : World I} (h : Extends P Q)
    (a : TypedExtraDownsets.Packed I P) (q : RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context))
    (hr : PackedRelated I above P a q) :
    PackedRelated I above Q (packedWeaken h a) (RenamingEquivariance.renamePacked (LogicalRelationWorlds.portRename h) q) := by
  rcases hr with ⟨t,rfl,ht⟩
  exact ⟨futureSyntax h t,rfl,LogicalRelationWorldsProof.relatedWeakening Symbol inferInstance arity I above a.1.val P Q h a.2 t ht⟩

theorem inputWeakening : ConstructorInputLogicalRelationTargets.InputWeakening := by
  intro Symbol inst arity I above f P Q h a base types extras ha
  constructor
  · intro i
    rw [argumentAtRename]
    exact LogicalRelationWorldsProof.relatedWeakening Symbol inst arity I above _ P Q h (a.1 i) (argumentAt base i) (ha.1 i)
  · intro p hp
    obtain ⟨b,hb,hpb⟩ := (TypedExtraDownsetsProof.packedImageCalibration Symbol inst arity I P Q h a.2 p).mp hp
    obtain ⟨q,hq,hr⟩ := ha.2 b hb
    refine ⟨RenamingEquivariance.renamePacked (LogicalRelationWorlds.portRename h) q,?_,?_⟩
    · rw [RenamingEquivarianceProof.argumentListRename]
      exact List.mem_map.mpr ⟨q,hq,rfl⟩
    · exact packedDownward Symbol inst arity I above Q p _ _ hpb (packedWeakenRelated above h b q hr)

theorem bottomFamilySound : ConstructorInputLogicalRelationTargets.BottomFamilySound := by
  intro Symbol inst arity I above f τ P a base types extras ha
  exact ActualValueLogicalRelationProof.bottom above τ.val P (.marked f.val τ.val base types extras)

theorem familyDownward : ConstructorInputLogicalRelationTargets.FamilyDownward := by
  intro Symbol inst arity I above M N hMN hN f τ P a base types extras ha
  exact ActualValueLogicalRelationProof.downward above τ.val P _ _ _ (hMN f τ P a) (hN f τ P a base types extras ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationProof

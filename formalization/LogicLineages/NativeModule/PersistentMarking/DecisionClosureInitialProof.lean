module

public import LogicLineages.NativeModule.PersistentMarking.DecisionClosureTargets
public import LogicLineages.NativeModule.PersistentMarking.PortNormalizationProof
public import LogicLineages.NativeModule.PersistentMarking.PortErasureProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionClosureInitialProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations DecisionRequests PortNormalization RefinementRenamingTargets

mutual
 theorem renameIdentity (q : Expr) : rename (fun _ x => x) q = q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ q => simpa only [RefinementRenameSupport.renameLam] using congrArg (Expr.lam σ) (renameIdentity q)
  | head f qs => simpa only [RefinementRenameSupport.renameHead] using congrArg (Expr.head f) (renameIdentityArgs qs)
  | marked f τ qs es => simpa only [RefinementRenameSupport.renameMarked] using congr (congrArg (Expr.marked f τ) (renameIdentityArgs qs)) (renameIdentityArgs es)
 termination_by sizeOf q
 theorem renameIdentityArgs (qs : Args) : renameArgs (fun _ x => x) qs = qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simpa only [RefinementRenameSupport.renameCons] using congr (congrArg Args.cons (renameIdentity q)) (renameIdentityArgs qs)
 termination_by sizeOf qs
end

theorem blankUsed (B : Nat) : used (blank B) = 0 := by
  induction B with
  | zero => rfl
  | succ B ih => simpa only [blank,List.replicate_succ,used] using ih

theorem blankWellFormed (K : List Ty) (B : Nat) : WellFormed K B (blank B) := by
  refine ⟨by simp [blank],?_⟩
  intro i σ hi
  have hm : some σ ∈ blank B := List.mem_of_getElem? hi
  simp [blank] at hm

theorem initial : DecisionClosureTargets.InitialState := by
  intro S F
  have hinit := DecisionSourceBasicProof.initial F.source F.target F.sourceType F.targetType
    F.sourcePaper.1 F.targetPaper.1 F.sourceOrdinary F.targetOrdinary
  have ho : Observed F (blank F.data.ports) F.target := by
    apply (DecisionObservationProof.enumeration _ _ _ _ _ _).mpr
    refine ⟨[],F.target,.nil,.root,.nil,rfl,?_,?_⟩
    · rw [blankUsed]; exact Nat.le_refl _
    · exact (SubstitutionProof.emptySubstitution F.target 0).symm
  have h : Invariant F (.weak (blank F.data.ports) F.source F.target) :=
    ⟨blankWellFormed _ _,hinit.2,ho⟩
  exact ⟨h,h⟩

theorem equivalence : DecisionClosureTargets.InitialEquivalence := by
  intro S F
  have h := (initial S F).1
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro hw
    have hn := PortNormalizationProof.weak S F _ _ hw (fun _ x => x) _
      (fun _ _ _ he => he) h.1 (by simpa only [renameIdentity] using h.2.1)
      (by simpa only [renameIdentity] using h.2.2)
    simpa only [renameIdentity] using hn
  · exact PortErasureProof.weak _ _ _ _ _ _
  · intro hs
    have hn := PortNormalizationProof.strict S F _ _ hs (fun _ x => x) _
      (fun _ _ _ he => he) h.1 (by simpa only [renameIdentity] using h.2.1)
      (by simpa only [renameIdentity] using h.2.2)
    simpa only [renameIdentity] using hn
  · exact PortErasureProof.strict _ _ _ _ _ _
end LogicLineages.PersistentMarking.DecisionClosureInitialProof

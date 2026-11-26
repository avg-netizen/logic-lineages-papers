import LogicLineages.PersistentMarking.RefinementRenamingTargets
import LogicLineages.PersistentMarking.FreeTypingProof
import LogicLineages.PersistentMarking.FreeCompositionProof
namespace LogicLineages.PersistentMarking.RefinementRenameSupport
open Spine NameBridge RefinementRenamingTargets

mutual
 theorem depth (π : NameRenaming) (d : Nat) (q : Expr) :
    freeSub (fun σ x => .free σ (π σ x)) d q = rename π q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ body => exact congrArg (Expr.lam σ) ((depth π (d+1) body).trans (depth π 1 body).symm)
  | head f base => exact congrArg (Expr.head f) (depthArgs π d base)
  | marked f τ base extras => exact congr (congrArg (Expr.marked f τ) (depthArgs π d base)) (depthArgs π d extras)
 termination_by sizeOf q
 theorem depthArgs (π : NameRenaming) (d : Nat) (qs : Args) :
    freeSubArgs (fun σ x => .free σ (π σ x)) d qs = renameArgs π qs := by
  cases qs with
  | nil => rfl
  | cons q qs => exact congr (congrArg Args.cons (depth π d q)) (depthArgs π d qs)
 termination_by sizeOf qs
end

@[simp] theorem renameFree (π : NameRenaming) (σ : Ty) (x : Nat) : rename π (.free σ x) = .free σ (π σ x) := rfl
@[simp] theorem renameLam (π : NameRenaming) (σ : Ty) (q : Expr) : rename π (.lam σ q) = .lam σ (rename π q) := by
  exact congrArg (Expr.lam σ) (depth π 1 q)
@[simp] theorem renameHead (π : NameRenaming) (f : Head) (qs : Args) : rename π (.head f qs) = .head f (renameArgs π qs) := rfl
@[simp] theorem renameMarked (π : NameRenaming) (f : Head) (τ : Ty) (base extras : Args) : rename π (.marked f τ base extras) = .marked f τ (renameArgs π base) (renameArgs π extras) := rfl
@[simp] theorem renameNil (π : NameRenaming) : renameArgs π .nil = .nil := rfl
@[simp] theorem renameCons (π : NameRenaming) (q : Expr) (qs : Args) : renameArgs π (.cons q qs) = .cons (rename π q) (renameArgs π qs) := rfl

theorem renameType (π : NameRenaming) (q : Expr) : (rename π q).type = q.type := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ q => simp only [renameLam,Expr.type,renameType π q]
  | head f qs => rfl
  | marked f τ qs es => rfl
termination_by sizeOf q

mutual
 theorem valid (S : Signature) (π : NameRenaming) (q : Expr) (h : Valid S q) : Valid S (rename π q) := by
  cases q with
  | free σ x => trivial
  | bound σ i => trivial
  | lam σ q => simpa only [renameLam,Valid] using valid S π q h
  | head f qs => exact ⟨h.1,validArgs S π qs h.2⟩
  | marked f τ qs es => exact ⟨h.1,validArgs S π qs h.2.1,validArgs S π es h.2.2⟩
 termination_by sizeOf q
 theorem validArgs (S : Signature) (π : NameRenaming) (qs : Args) (h : ValidArgs S qs) : ValidArgs S (renameArgs π qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨valid S π q h.1,validArgs S π qs h.2⟩
 termination_by sizeOf qs
end

theorem paper (S : Signature) (π : NameRenaming) (q : Expr) (σ : Ty) (h : PaperTerm S q σ) : PaperTerm S (rename π q) σ :=
  ⟨FreeTypingProof.freeSubTyped EmptyContext _ (fun _ _ => .free) q σ h.1, valid S π q h.2⟩

theorem nameEq (π : NameRenaming) (hi : injectiveNames π) (σ τ : Ty) (x y : Nat) :
    ((σ,π σ x) = (τ,π τ y)) ↔ ((σ,x) = (τ,y)) := by
  constructor
  · intro h
    have ht : σ = τ := congrArg Prod.fst h
    subst τ
    have hn := congrArg Prod.snd h
    exact congrArg (fun z => (σ,z)) (hi σ x y hn)
  · intro h
    cases h
    rfl

mutual
 theorem occurs (π : NameRenaming) (hi : injectiveNames π) (σ : Ty) (x : Nat) (q : Expr) :
    freeOccurs (σ,π σ x) (rename π q) = freeOccurs (σ,x) q := by
  cases q with
  | free τ y => simp only [renameFree,freeOccurs,nameEq π hi σ τ x y]
  | bound τ i => rfl
  | lam τ q => simp only [renameLam,freeOccurs,occurs π hi σ x q]
  | head f qs => exact occursArgs π hi σ x qs
  | marked f τ qs es => simp only [renameMarked,freeOccurs,occursArgs π hi σ x qs,occursArgs π hi σ x es]
 termination_by sizeOf q
 theorem occursArgs (π : NameRenaming) (hi : injectiveNames π) (σ : Ty) (x : Nat) (qs : Args) :
    freeOccursArgs (σ,π σ x) (renameArgs π qs) = freeOccursArgs (σ,x) qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [renameCons,freeOccursArgs,occurs π hi σ x q,occursArgs π hi σ x qs]
 termination_by sizeOf qs
end

theorem opening (π : NameRenaming) (σ : Ty) (x : Nat) (q : Expr) :
    rename π (openBody σ x q) = openBody σ (π σ x) (rename π q) := by
  have h := FreeCompositionProof.composition (fun τ y => Expr.free τ (π τ y)) (.cons (.free σ x) .nil) 0 q
  simpa only [depth,freeSubArgs,freeSub,shift,openBody] using h

theorem mapAt (π : NameRenaming) {qs i q} (h : At qs i q) : At (renameArgs π qs) i (rename π q) := by
  induction h with
  | here => exact .here
  | there h ih => exact .there ih
end LogicLineages.PersistentMarking.RefinementRenameSupport

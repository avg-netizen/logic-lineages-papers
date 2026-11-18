import LogicLineages.PersistentMarking.RefinementOpeningProof
namespace LogicLineages.PersistentMarking.PortRenameProof
open Spine NameBridge RefinementRenamingTargets RefinementRenameSupport

def compose (ρ π : NameRenaming) : NameRenaming := fun σ x => ρ σ (π σ x)

theorem injectiveCompose (ρ π : NameRenaming) (hr : injectiveNames ρ)
    (hp : injectiveNames π) : injectiveNames (compose ρ π) := by
  intro σ x y h
  exact hp σ x y (hr σ (π σ x) (π σ y) h)

mutual
 theorem composition (ρ π : NameRenaming) (q : Expr) :
    rename (compose ρ π) q = rename ρ (rename π q) := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ q => simpa only [renameLam] using congrArg (Expr.lam σ) (composition ρ π q)
  | head f qs => simpa only [renameHead] using congrArg (Expr.head f) (compositionArgs ρ π qs)
  | marked f σ qs es =>
    simp only [renameMarked]
    exact congr (congrArg (Expr.marked f σ) (compositionArgs ρ π qs)) (compositionArgs ρ π es)
 termination_by sizeOf q
 theorem compositionArgs (ρ π : NameRenaming) (qs : Args) :
    renameArgs (compose ρ π) qs = renameArgs ρ (renameArgs π qs) := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    simp only [renameCons]
    exact congr (congrArg Args.cons (composition ρ π q)) (compositionArgs ρ π qs)
 termination_by sizeOf qs
end

/- The swap acts only after the actual child renaming. Both absence premises
refer to the renamed parent, not to a separately transported derivation. -/
def adjusted (π : NameRenaming) (σ : Ty) (x y : Nat) : NameRenaming :=
  compose (RefinementOpeningProof.swap σ (π σ x) y) π

theorem adjustedInjective (π : NameRenaming) (σ : Ty) (x y : Nat)
    (hp : injectiveNames π) : injectiveNames (adjusted π σ x y) :=
  injectiveCompose _ _ (RefinementOpeningProof.swapInjective _ _ _) hp

theorem adjustedParent (π : NameRenaming) (σ : Ty) (x y : Nat) (q : Expr)
    (hx : freeOccurs (σ,π σ x) (rename π q) = false)
    (hy : freeOccurs (σ,y) (rename π q) = false) :
    rename (adjusted π σ x y) q = rename π q := by
  rw [adjusted,composition]
  exact RefinementOpeningProof.absent _ _ _ _ hx hy

theorem adjustedOpening (π : NameRenaming) (σ : Ty) (x y : Nat) (q : Expr)
    (hx : freeOccurs (σ,π σ x) (rename π q) = false)
    (hy : freeOccurs (σ,y) (rename π q) = false) :
    rename (adjusted π σ x y) (openBody σ x q) = openBody σ y (rename π q) := by
  rw [adjusted,composition,opening]
  exact RefinementOpeningProof.opened _ _ _ _ hx hy
end LogicLineages.PersistentMarking.PortRenameProof

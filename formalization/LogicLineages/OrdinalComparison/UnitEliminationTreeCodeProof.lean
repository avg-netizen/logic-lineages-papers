module
public import LogicLineages.OrdinalComparison.UnitEliminationTreeCodeFoldProof
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode.Proof

private theorem mod_tag (a tag : Nat) (h : tag<4) : (4*a+tag)%4=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<4) : (4*a+tag)/4=a := by omega

private theorem fold_leaf_data (leaf : Nat → Nat) (free : Nat → Nat → Nat)
    (active : Nat → Nat → Nat → Nat) (p : Nat) :
    fold leaf free active (leafCode p)=leaf p := by
  rw [fold.eq_def]
  simp [leafCode]
private theorem fold_free_data (leaf : Nat → Nat) (free : Nat → Nat → Nat)
    (active : Nat → Nat → Nat → Nat) (p q : Nat) :
    fold leaf free active (freeCode p q)=free p (fold leaf free active q) := by
  rw [fold.eq_def]
  simp [freeCode,mod_tag _ 1 (by decide),div_tag _ 1 (by decide)]
private theorem fold_active_data (leaf : Nat → Nat) (free : Nat → Nat → Nat)
    (active : Nat → Nat → Nat → Nat) (p q r : Nat) :
    fold leaf free active (activeCode p q r)=active p (fold leaf free active q) (fold leaf free active r) := by
  rw [fold.eq_def]
  simp [activeCode,mod_tag _ 2 (by decide),div_tag _ 2 (by decide)]

theorem exactTreeFold : Targets.ExactTreeFold := by
  intro α inst Γ q leaf free active
  induction q with
  | leaf b => exact fold_leaf_data leaf free active _
  | free left right σ d q ih =>
    rw [code,fold_free_data,ih]
    rfl
  | active left right σ p d d' c q r ihq ihr =>
    rw [code,fold_active_data,ihq,ihr]
    rfl

theorem exactAnchorRealization : Targets.ExactAnchorRealization := by
  constructor
  · have hd : Primrec (fun n : Nat =>
        (Encodable.decode (α := UnitGroundBlockCode.Payload (Nat×Nat)) n).getD (0,0,0,0,(0,0))) :=
      Primrec.option_getD.comp Primrec.decode (Primrec.const _)
    have hleaf : Computable realizeLeaf :=
      effectiveConstructorsAndFold.1.to_comp.comp (Computable.encode.comp
        (UnitGroundBlockCode.Proof.effectiveAlgorithms.2.2.2.2.2.comp hd.to_comp))
    exact effectiveConstructorsAndFold.2.2.2.2 realizeLeaf freeCode activeCode hleaf
      effectiveConstructorsAndFold.2.1.to_comp effectiveConstructorsAndFold.2.2.1.to_comp
  · intro Γ q
    unfold realizeCode
    rw [exactTreeFold]
    induction q with
    | leaf b =>
      simp only [treeFold,realizeLeaf,Encodable.encodek,Option.getD_some]
      rfl
    | free left right σ d q ih =>
      simp only [treeFold,UnitElimination.realize,UnitElimination.mapAnchors,code] at ih ⊢
      rw [ih]
    | active left right σ p d d' c q r ihq ihr =>
      simp only [treeFold,UnitElimination.realize,UnitElimination.mapAnchors,code] at ihq ihr ⊢
      rw [ihq,ihr]
end LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode.Proof

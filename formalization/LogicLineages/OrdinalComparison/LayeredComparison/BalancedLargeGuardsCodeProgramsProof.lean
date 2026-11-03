module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
public import LogicLineages.OrdinalComparison.RawComparisonProof
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode.Proof
open CommonHeadLargeGuards (masks maskCoefficient)
open CommonHeadCode (constant conjunction disjunction negative conjoin disjoin)
open CommonHeadCode.Program
open IntegerAlgorithms.Proof (sign_primitive)

attribute [local irreducible] Nat.sqrt Nat.unpair rawComparisonCode

private theorem atom_primitive (op : Nat) :
    Primrec₂ (fun i j : Nat => ([(op,i,j)] : Code)) :=
  Primrec.list_cons.comp ((Primrec.const op).pair Primrec.id) (Primrec.const [])

private theorem head_primitive : Primrec₂ headCode := Primrec.list_getD 0

attribute [local irreducible] headCode

private theorem key_equal_primitive :
    Primrec (fun p : List Nat × Nat × Nat => keyEqualCode p.1 p.2.1 p.2.2) := by
  let D := List Nat × Nat × Nat
  have hi : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  have hleft : Primrec (fun p : D => headCode p.1 p.2.1) :=
    head_primitive.comp Primrec.fst hi
  have hright : Primrec (fun p : D => headCode p.1 p.2.2) :=
    head_primitive.comp Primrec.fst hj
  exact Primrec.ite (Primrec.eq.comp hleft hright)
    ((atom_primitive 2).comp hi hj) (Primrec.const (constant false))

private theorem key_less_primitive :
    Primrec (fun p : List Nat × Nat × Nat => keyLessCode p.1 p.2.1 p.2.2) := by
  let D := List Nat × Nat × Nat
  have hi : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  have hleft : Primrec (fun p : D => headCode p.1 p.2.1) :=
    head_primitive.comp Primrec.fst hi
  have hright : Primrec (fun p : D => headCode p.1 p.2.2) :=
    head_primitive.comp Primrec.fst hj
  have hraw : Primrec₂ rawComparisonCode := rawComparisonPrimitiveRecursive
  have hcompare : Primrec (fun p : D =>
      rawComparisonCode (headCode p.1 p.2.1) (headCode p.1 p.2.2)) :=
    hraw.comp hleft hright
  exact Primrec.ite (Primrec.eq.comp hcompare (Primrec.const 0))
    (Primrec.const (constant true))
    (Primrec.ite (Primrec.eq.comp hleft hright)
      ((atom_primitive 3).comp hi hj) (Primrec.const (constant false)))

attribute [local irreducible] keyEqualCode keyLessCode

private theorem mask_primitive : Primrec (fun p : List Nat × Nat × Nat × List Bool =>
    maskCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := List Nat × Nat × Nat × List Bool
  have hm : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hmask : Primrec (fun p : D => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hindices : Primrec (fun p : D × Nat => (p.1.2.2.1,p.2)) :=
    (hi.comp Primrec.fst).pair Primrec.snd
  have hkeyargs : Primrec (fun p : D × Nat => (p.1.1,p.1.2.2.1,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair hindices
  have hkey : Primrec (fun p : D × Nat => keyEqualCode p.1.1 p.1.2.2.1 p.2) :=
    key_equal_primitive.comp hkeyargs
  have hflag : Primrec (fun p : D × Nat => p.1.2.2.2.getD p.2 false) :=
    (Primrec.list_getD false).comp (hmask.comp Primrec.fst) Primrec.snd
  have heach : Primrec₂ (fun p : D => fun j : Nat =>
      if p.2.2.2.getD j false then keyEqualCode p.1 p.2.2.1 j
      else negative (keyEqualCode p.1 p.2.2.1 j)) := by
    apply (Primrec.cond hflag hkey (negative_primitive.comp hkey)).of_eq
    intro p
    dsimp only
    cases p.1.2.2.2.getD p.2 false <;> rfl
  exact conjoin_primitive.comp
    (Primrec.list_map (Primrec.list_range.comp hm) heach)

attribute [local irreducible] maskCode

private theorem selected_masks_primitive : Primrec (fun p : List Int × Int =>
    (masks p.1.length).filter (fun mask => Int.sign (maskCoefficient p.1 mask) = p.2)) := by
  have hsign : Primrec (fun p : List Bool × (List Int × Int) =>
      Int.sign (maskCoefficient p.2.1 p.1)) :=
    sign_primitive.comp
      (coefficient_primitive.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
  have hpred : PrimrecRel (fun mask : List Bool => fun p : List Int × Int =>
      Int.sign (maskCoefficient p.1 mask) = p.2) :=
    Primrec.eq.comp hsign (Primrec.snd.comp Primrec.snd)
  exact hpred.listFilter.comp
    (masks_primitive.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id

private theorem block_primitive : Primrec (fun p : List Nat × List Int × Nat × Int =>
    blockCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := List Nat × List Int × Nat × Int
  have hcs : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : D => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hfilter : Primrec (fun p : D => (masks p.2.1.length).filter
      (fun mask => Int.sign (maskCoefficient p.2.1 mask) = p.2.2.2)) :=
    selected_masks_primitive.comp (hcs.pair hd)
  have htail : Primrec (fun p : D × List Bool => (p.1.2.2.1,p.2)) :=
    (hi.comp Primrec.fst).pair Primrec.snd
  have hbody : Primrec (fun p : D × List Bool =>
      (p.1.2.1.length,p.1.2.2.1,p.2)) :=
    (Primrec.list_length.comp (hcs.comp Primrec.fst)).pair htail
  have hargs : Primrec (fun p : D × List Bool =>
      (p.1.1,p.1.2.1.length,p.1.2.2.1,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair hbody
  have heach : Primrec₂ (fun p : D => fun mask : List Bool =>
      maskCode p.1 p.2.1.length p.2.2.1 mask) := mask_primitive.comp hargs
  exact disjoin_primitive.comp (Primrec.list_map hfilter heach)

attribute [local irreducible] blockCode

private theorem canceled_primitive : Primrec₂ canceledCode := by
  let D := List Nat × List Int
  have htail : Primrec (fun p : D × Nat => (p.2,(0 : Int))) :=
    Primrec.snd.pair (Primrec.const 0)
  have hbody : Primrec (fun p : D × Nat => (p.1.2,p.2,(0 : Int))) :=
    (Primrec.snd.comp Primrec.fst).pair htail
  have hargs : Primrec (fun p : D × Nat => (p.1.1,p.1.2,p.2,(0 : Int))) :=
    (Primrec.fst.comp Primrec.fst).pair hbody
  have heach : Primrec₂ (fun p : D => fun i : Nat => blockCode p.1 p.2 i 0) :=
    block_primitive.comp hargs
  exact conjoin_primitive.comp (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) heach)

private theorem maximal_primitive : Primrec (fun p : List Nat × List Int × Nat =>
    maximalCode p.1 p.2.1 p.2.2) := by
  let D := List Nat × List Int × Nat
  have hcs : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  have hindices : Primrec (fun p : D × Nat => (p.1.2.2,p.2)) :=
    (hi.comp Primrec.fst).pair Primrec.snd
  have hkeyargs : Primrec (fun p : D × Nat => (p.1.1,p.1.2.2,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair hindices
  have hkey : Primrec (fun p : D × Nat => keyLessCode p.1.1 p.1.2.2 p.2) :=
    key_less_primitive.comp hkeyargs
  have htail : Primrec (fun p : D × Nat => (p.2,(0 : Int))) :=
    Primrec.snd.pair (Primrec.const 0)
  have hbody : Primrec (fun p : D × Nat => (p.1.2.1,p.2,(0 : Int))) :=
    (hcs.comp Primrec.fst).pair htail
  have hblockargs : Primrec (fun p : D × Nat => (p.1.1,p.1.2.1,p.2,(0 : Int))) :=
    (Primrec.fst.comp Primrec.fst).pair hbody
  have hblock : Primrec (fun p : D × Nat => blockCode p.1.1 p.1.2.1 p.2 0) :=
    block_primitive.comp hblockargs
  have heach : Primrec₂ (fun p : D => fun j : Nat =>
      disjunction (negative (keyLessCode p.1 p.2.2 j)) (blockCode p.1 p.2.1 j 0)) :=
    disjunction_primitive.comp (negative_primitive.comp hkey) hblock
  exact conjoin_primitive.comp (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp hcs)) heach)

attribute [local irreducible] canceledCode maximalCode

private theorem difference_primitive : Primrec (fun p : Nat × Nat × Int =>
    differenceSignCode p.1 p.2.1 p.2.2) := by
  let D := Nat × Nat × Int
  have hr : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp hd (Primrec.const (-1 : Int)))
    ((atom_primitive 3).comp Primrec.fst hr)
    (Primrec.ite (Primrec.eq.comp hd (Primrec.const (0 : Int)))
      ((atom_primitive 2).comp Primrec.fst hr)
      (Primrec.ite (Primrec.eq.comp hd (Primrec.const (1 : Int)))
        ((atom_primitive 3).comp hr Primrec.fst) (Primrec.const (constant false))))

attribute [local irreducible] differenceSignCode

private theorem sign_code_primitive : Primrec (fun p : List Nat × List Int × Int =>
    signCode p.1 p.2.1 p.2.2) := by
  let D := List Nat × List Int × Int
  have hcs : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlen : Primrec (fun p : D => p.2.1.length) := Primrec.list_length.comp hcs
  have hdiffTail : Primrec (fun p : D => (p.2.1.length + 1,p.2.2)) :=
    (Primrec.succ.comp hlen).pair hd
  have hdiffArgs : Primrec (fun p : D => (p.2.1.length,p.2.1.length + 1,p.2.2)) :=
    hlen.pair hdiffTail
  have hdiff : Primrec (fun p : D => differenceSignCode p.2.1.length
      (p.2.1.length + 1) p.2.2) := difference_primitive.comp hdiffArgs
  have hcancel : Primrec (fun p : D => canceledCode p.1 p.2.1) :=
    canceled_primitive.comp Primrec.fst hcs
  have hleft : Primrec (fun p : D => conjunction (canceledCode p.1 p.2.1)
      (differenceSignCode p.2.1.length (p.2.1.length + 1) p.2.2)) :=
    conjunction_primitive.comp hcancel hdiff
  have htail : Primrec (fun p : D × Nat => (p.2,p.1.2.2)) :=
    Primrec.snd.pair (hd.comp Primrec.fst)
  have hbody : Primrec (fun p : D × Nat => (p.1.2.1,p.2,p.1.2.2)) :=
    (hcs.comp Primrec.fst).pair htail
  have hblockArgs : Primrec (fun p : D × Nat => (p.1.1,p.1.2.1,p.2,p.1.2.2)) :=
    (Primrec.fst.comp Primrec.fst).pair hbody
  have hblock : Primrec (fun p : D × Nat => blockCode p.1.1 p.1.2.1 p.2 p.1.2.2) :=
    block_primitive.comp hblockArgs
  have hmaxTail : Primrec (fun p : D × Nat => (p.1.2.1,p.2)) :=
    (hcs.comp Primrec.fst).pair Primrec.snd
  have hmaxArgs : Primrec (fun p : D × Nat => (p.1.1,p.1.2.1,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair hmaxTail
  have hmax : Primrec (fun p : D × Nat => maximalCode p.1.1 p.1.2.1 p.2) :=
    maximal_primitive.comp hmaxArgs
  have heach : Primrec₂ (fun p : D => fun i : Nat =>
      conjunction (blockCode p.1 p.2.1 i p.2.2) (maximalCode p.1 p.2.1 i)) :=
    conjunction_primitive.comp hblock hmax
  have hmany : Primrec (fun p : D => disjoin ((List.range p.2.1.length).map
      (fun i => conjunction (blockCode p.1 p.2.1 i p.2.2) (maximalCode p.1 p.2.1 i)))) :=
    disjoin_primitive.comp (Primrec.list_map (Primrec.list_range.comp hlen) heach)
  have hright : Primrec (fun p : D => if p.2.2 = 0 then constant false
      else disjoin ((List.range p.2.1.length).map
        (fun i => conjunction (blockCode p.1 p.2.1 i p.2.2) (maximalCode p.1 p.2.1 i)))) :=
    Primrec.ite (Primrec.eq.comp hd (Primrec.const 0)) (Primrec.const (constant false)) hmany
  exact disjunction_primitive.comp hleft hright

attribute [local irreducible] signCode

private theorem large_primitive : Primrec (fun p : Nat × List Nat × List Int × Int =>
    largeCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := Nat × List Nat × List Int × Int
  have hcs : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hbound : Primrec₂ (fun p : D => fun i : Nat => ([(4,p.1,i)] : Code)) :=
    (atom_primitive 4).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hbounds : Primrec (fun p : D => conjoin
      ((List.range p.2.2.1.length).map (fun i => [(4,p.1,i)]))) :=
    conjoin_primitive.comp (Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp hcs)) hbound)
  have hsign : Primrec (fun p : D => signCode p.2.1 p.2.2.1 p.2.2.2) :=
    sign_code_primitive.comp Primrec.snd
  exact conjunction_primitive.comp hbounds hsign

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨head_primitive, key_equal_primitive, key_less_primitive, mask_primitive,
    block_primitive, canceled_primitive, maximal_primitive, difference_primitive,
    sign_code_primitive, large_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode.Proof

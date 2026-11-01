module
public import LogicLineages.ModelsAlgebra.PGroups.CofinalSocleMapTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionProof
public import LogicLineages.ModelsAlgebra.PGroups.AdaptedSocleDefinitions
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem subspace_outside_finite_span (K V:Type) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] (W:Submodule K V) [Infinite W]
    (n:ℕ) (v:Fin n→V) : ∃x:W,(x:V)∉Submodule.span K (Set.range v) := by
  classical
  let S := Submodule.span K (Set.range v)
  letI : Module.Finite K S := Module.Finite.span_of_finite K (Set.finite_range v)
  letI : Finite S := Module.finite_of_finite K
  by_contra! hn
  let f : W→S := fun x=>⟨x,hn x⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z:S=>(z:V)) h
  letI : Finite W := Finite.of_injective f hf
  exact not_finite W

noncomputable def independentStageStep (K V:Type) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] (W:ℕ→Submodule K V) (h:∀n,Infinite (W n))
    (n:ℕ) (prev:∀m:ℕ,m<n→V) : V := by
  letI := h n
  exact (Classical.choose (subspace_outside_finite_span K V (W n) n
    (fun i:Fin n=>prev i.val i.isLt)):W n).val

noncomputable def independentStageSequence (K V:Type) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] (W:ℕ→Submodule K V) (h:∀n,Infinite (W n)) : ℕ→V :=
  Nat.lt_wfRel.wf.fix (independentStageStep K V W h)

private theorem independent_stage_spec (K V:Type) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] (W:ℕ→Submodule K V) (h:∀n,Infinite (W n)) (n:ℕ) :
    independentStageSequence K V W h n∈W n ∧
      independentStageSequence K V W h n∉Submodule.span K
        (Set.range (fun i:Fin n=>independentStageSequence K V W h i)) := by
  classical
  letI := h n
  have he := WellFounded.fix_eq Nat.lt_wfRel.wf (independentStageStep K V W h) n
  change independentStageSequence K V W h n = _ at he
  constructor
  · rw [he]
    unfold independentStageStep
    exact (Classical.choose (subspace_outside_finite_span K V (W n) n
      (fun i:Fin n=>independentStageSequence K V W h i))).property
  · rw [he]
    unfold independentStageStep
    exact Classical.choose_spec (subspace_outside_finite_span K V (W n) n
      (fun i:Fin n=>independentStageSequence K V W h i))

private theorem independent_stage_linearIndependent (K V:Type) [Field K] [Finite K]
    [AddCommGroup V] [Module K V] (W:ℕ→Submodule K V) (h:∀n,Infinite (W n)) :
    LinearIndependent K (independentStageSequence K V W h) := by
  classical
  let v := independentStageSequence K V W h
  have hfin : ∀n,LinearIndependent K (fun i:Fin n=>v i) := by
    intro n
    induction n with
    | zero => exact linearIndependent_empty_type
    | succ n ih =>
      have hh := ih.finSnoc (independent_stage_spec K V W h n).2
      convert hh using 1
      ext i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simp [v]
      · simp [v]
  rw [←linearIndepOn_univ_iff]
  apply linearIndepOn_of_finite
  intro t ht htf
  obtain ⟨N,hN⟩ := htf.bddAbove
  exact (hfin (N+1)).comp (fun i:t=>⟨i.val,Nat.lt_succ_of_le (hN i.property)⟩)
    (by intro x y hxy;apply Subtype.ext;exact congrArg Fin.val hxy)

/-- Enumerate every level/target-socle requirement, choose independent source
socle vectors meeting them, and extend their linear assignment twice by the
proved divisible-group extension theorem. -/
theorem cofinal_socle_surjective_hom : Targets.cofinalSocleSurjectiveHom := by
  classical
  intro p _ B C _ _ _ _ δ _ hδ hd hinf
  let V := pSocle p (⊤ : AddSubgroup B)
  let W := pSocle p (⊤ : AddSubgroup C)
  letI : Countable (Set.Iio δ) := Ordinal.ToType.mk.injective.countable
  let Req := Set.Iio δ × W
  letI : Encodable Req := Encodable.ofCountable Req
  let d : Req := (⟨0,hδ⟩,0)
  let req : ℕ→Req := fun n=>(Encodable.decode (α:=Req) n).getD d
  have hreq (r:Req) : req (Encodable.encode r)=r := by simp [req,Encodable.encodek]
  let S : ℕ→Submodule (ZMod p) V := fun n=>AddSubgroup.toZModSubmodule p
    ((transfiniteFiltration p (req n).1.val:AddSubgroup B).comap (pSocle p (⊤:AddSubgroup B)).subtype)
  have hS (n:ℕ) : Infinite (S n) := by
    letI := hinf (req n).1.val (req n).1.property
    let j : pSocle p (transfiniteFiltration p (req n).1.val:AddSubgroup B)→S n :=
      fun x=>⟨⟨x.val,⟨AddSubgroup.mem_top _,x.property.2⟩⟩,x.property.1⟩
    apply Infinite.of_injective j
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z:S n=>((z:V):B)) hxy
  let v := independentStageSequence (ZMod p) V S hS
  have hv := independent_stage_linearIndependent (ZMod p) V S hS
  let U := Submodule.span (ZMod p) (Set.range v)
  let e : Module.Basis ℕ (ZMod p) U := Module.Basis.span hv
  let l : U→ₗ[ZMod p] W := e.constr (ZMod p) (fun n=>(req n).2)
  let j : U→+C := (pSocle p (⊤:AddSubgroup C)).subtype.comp l.toAddMonoidHom
  obtain ⟨g,hg⟩ := divisible_hom_extension V C hd U.toAddSubgroup j
  obtain ⟨f,hf⟩ := divisible_hom_extension B C hd (pSocle p ⊤) g
  have hmap (n:ℕ) : f ((v n:V):B)=((req n).2:C) := by
    rw [hf (v n)]
    let u : U := ⟨v n,Submodule.subset_span (Set.mem_range_self n)⟩
    change g (u:V)=_
    rw [hg u]
    change ((l u:W):C)=_
    have hh := congrArg (fun w:W=>(w:C)) (e.constr_basis (ZMod p) (fun n=>(req n).2) n)
    have heq : e n=u := by
      apply Subtype.ext
      exact Module.Basis.coe_span_apply hv n
    change ((l (e n):W):C)=_ at hh
    rw [heq] at hh
    exact hh
  refine ⟨f,?_⟩
  intro β hβ c
  let r : Req := (⟨β,hβ⟩,c)
  let n := Encodable.encode r
  have hr : req n=r := hreq r
  have hb : ((v n:V):B)∈(transfiniteFiltration p β:AddSubgroup B) := by
    have hh := (independent_stage_spec (ZMod p) V S hS n).1
    change ((v n:V):B)∈(transfiniteFiltration p (req n).1.val:AddSubgroup B) at hh
    simpa only [hr] using hh
  refine ⟨⟨(v n:V),⟨hb,(v n).property.2⟩⟩,?_⟩
  simpa only [hr] using hmap n
end LogicLineages.ModelsAlgebra.PGroups

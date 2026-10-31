module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionEvenTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionOddProof
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneOddProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

private theorem one_iso_left {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (e : X ≃+ Z) {n : ℕ} (a : Fin n → X) (b : Fin n → Y)
    (h : BackAndForth (1:Ordinal) a b) : BackAndForth (1:Ordinal) (fun i => e (a i)) b := by
  have hs := back_forth_successor 0 Z Y n (fun i => e (a i)) b
  simp only [zero_add] at hs
  apply hs.mpr (by
    intro m d
    obtain ⟨c,hc⟩ := (back_forth_successor 0 X Y n a b).mp (by simpa only [zero_add] using h) m d
    refine ⟨fun i => e (c i),?_⟩
    apply (zero_comparison Y Z (n+m) _ _).mpr
    have ha := back_forth_atomic 0 Y X (n+m) _ _ hc
    have he := embedding_atomic_agreement X Z e.toAddMonoidHom e.injective (n+m) (append a c)
    have hv : (fun i => e (append a c i)) = append (fun i => e (a i)) (fun i => e (c i)) := by
      funext i; induction i using Fin.addCases <;> simp [append]
    change AtomicAgreement (append a c) (fun i => e (append a c i)) at he
    rw [hv] at he
    exact fun s t => (ha s t).trans (he s t))

theorem terminal_deletion_even : Targets.terminalDeletionEven := by
  classical
  intro G _ _ p _ hG rG γ K T N hsplit hdis hN hbound hw htwo
  letI : Countable (G ⧸ T) := (QuotientAddGroup.mk'_surjective T).countable
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  let U : AddSubgroup (G ⧸ T) := transfiniteFiltration p δ
  have hbase := terminal_deletion_odd G p hG rG γ K T N hsplit hdis hN hbound hw
  have hRank := hbase.1
  have rQ := hbase.2.2.1
  have hlen := hbase.2.2.2.2.1
  have lG : StagesNonzeroBelow p G δ := fun α hα => (hlen α (hα.trans_le le_self_add)).1
  have lQ : StagesNonzeroBelow p (G ⧸ T) δ := fun α hα => (hlen α (hα.trans_le le_self_add)).2
  have hQ := p_primary_quotient G p T hG
  obtain ⟨ek,hek⟩ := coherent_terminal_quotient G p δ K T hsplit hdis
  have hδ : δ=0 ∨ Order.IsSuccLimit δ := by
    by_cases hz : γ=0
    · left; simp [δ,hz]
    · right; exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
        (lt_of_le_of_ne zero_le (Ne.symm hz))
  have heven : 2*γ+2 = (2*γ+1)+1 := by rw [add_assoc,one_add_one_eq_two]
  rw [heven]
  apply (back_forth_successor (2*γ+1) G (G ⧸ T) 0 _ _).mpr
  intro m d
  let D := AddSubgroup.closure (Set.range d)
  letI : Finite D := p_primary_finite_tuple_closure (G ⧸ T) p (Fact.out : p.Prime).ne_zero hQ m d
  let L : AddSubgroup (G ⧸ T) := D ⊓ U
  letI : Finite L := Finite.of_injective (AddSubgroup.inclusion (show L ≤ D from inf_le_left))
    (AddSubgroup.inclusion_injective _)
  letI : Fintype L := Fintype.ofFinite L
  let k := Fintype.card L
  let v : Fin k → L := (Fintype.equivFin L).symm
  let vU : Fin k → U := fun i => ⟨v i,(v i).property.2⟩
  let vK : Fin k → K := fun i => ek.symm (vU i)
  obtain ⟨c,hc⟩ := (back_forth_successor 1 S K 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).mp
    (by simpa only [one_add_one_eq_two] using htwo) k vK
  let bL : Fin (0+k) → L := append (fun i : Fin 0 => Fin.elim0 i) v
  let bU : Fin (0+k) → U := fun i => ⟨bL i,(bL i).property.2⟩
  let aS : Fin (0+k) → S := append (fun i : Fin 0 => Fin.elim0 i) c
  have hbL : Function.Surjective bL := by
    intro x
    obtain ⟨i,hi⟩ := (Fintype.equivFin L).symm.surjective x
    exact ⟨Fin.natAdd 0 i,by simpa only [bL,append,Fin.addCases_right,v] using hi⟩
  have hbu : (fun i => ek (append (fun i : Fin 0 => Fin.elim0 i) vK i)) = bU := by
    funext i
    induction i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i => simp only [append,vK,bU,bL,vU,Fin.addCases_right,AddEquiv.apply_symm_apply]
  have hbf : BackAndForth (1:Ordinal) bU aS := by
    have hh := one_iso_left ek _ _ hc
    rw [hbu] at hh
    exact hh
  obtain ⟨e0,he0⟩ := (atomic_generated_iso U S (0+k) bU aS).mp
    (back_forth_atomic 1 U S (0+k) _ _ hbf)
  let R := AddSubgroup.closure (Set.range bU)
  let j : L →+ U := {
    toFun := fun x => ⟨x,x.property.2⟩
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  have hjR (x : L) : j x ∈ R := by
    obtain ⟨i,rfl⟩ := hbL x
    exact AddSubgroup.subset_closure ⟨i,rfl⟩
  let jR := j.codRestrict R hjR
  let g : L →+ G := S.subtype.comp
    ((AddSubgroup.closure (Set.range aS)).subtype.comp (e0.toAddMonoidHom.comp jR))
  have hg : Function.Injective g := by
    intro x y h
    have h₁ := Subtype.ext h
    have h₂ := Subtype.ext h₁
    have h₃ := e0.injective h₂
    exact Subtype.ext (congrArg (fun z : R => (z:U).val) h₃)
  have hdeep (x : L) : g x ∈ S := (e0 (jR x)).val.property
  have hgmatch (i) : g (bL i) = (aS i:G) := by
    have hh := he0 i
    change (e0 (jR (bL i)) : S).val = (aS i:G)
    have hh' : (e0 (jR (bL i)) : S) = aS i := by
      change (e0 ⟨bU i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩ : S) = aS i
      exact hh
    exact congrArg Subtype.val hh'
  have hgp : ∀ (x : L), ∀ β ≤ δ,
      g x ∈ (transfiniteFiltration p β : AddSubgroup G) ↔
      (x:G ⧸ T) ∈ (transfiniteFiltration p β : AddSubgroup (G ⧸ T)) := by
    intro x β hβ
    exact iff_of_true (transfiniteFiltration_antitone p hβ (hdeep x))
      (transfiniteFiltration_antitone p hβ x.property.2)
  have hconstruct : ∃ F : D →+ G, Function.Injective F ∧
      (∀ x : L, F ⟨x,x.property.1⟩ = g x) ∧
      ∀ (x : D), ∀ β ≤ δ,
        F x ∈ (transfiniteFiltration p β : AddSubgroup G) ↔
        (x:G ⧸ T) ∈ (transfiniteFiltration p β : AddSubgroup (G ⧸ T)) := by
    rcases hδ with hz | hlim
    · have hDL : D ≤ L := fun x hx => ⟨hx,by simp [U,hz,transfiniteFiltration_zero]⟩
      let F := g.comp (AddSubgroup.inclusion hDL)
      exact ⟨F,hg.comp (AddSubgroup.inclusion_injective hDL),fun _ => rfl,
        fun x β hβ => hgp ⟨x,hDL x.property⟩ β hβ⟩
    · exact finite_below_limit_extension (G ⧸ T) G p hQ hG D L g.range
        (AddMonoidHom.ofInjective hg) δ hlim inf_le_left le_rfl hgp
        (fun α hα => (hRank α hα).symm.le)
  obtain ⟨F,hF,hFL,hFp⟩ := hconstruct
  let e : D ≃+ F.range := AddMonoidHom.ofInjective hF
  letI : Finite F.range := Finite.of_surjective e e.surjective
  have haR (i) : (aS i:G) ∈ F.range := ⟨⟨bL i,(bL i).property.1⟩,(hFL (bL i)).trans (hgmatch i)⟩
  have haenum (x : G) (hx : x ∈ F.range) (hxS : x ∈ S) : ∃ i, (aS i:G)=x := by
    obtain ⟨z,rfl⟩ := hx
    have hz : (z:G ⧸ T) ∈ U := (hFp z δ le_rfl).mp hxS
    obtain ⟨i,hi⟩ := hbL ⟨z,z.property,hz⟩
    refine ⟨i,?_⟩
    have hh := (hFL (bL i)).trans (hgmatch i)
    rw [hi] at hh
    exact hh.symm
  have hcompat (i) : (bU i:G ⧸ T) = (e.symm ⟨aS i,haR i⟩:G ⧸ T) := by
    have he : e ⟨bL i,(bL i).property.1⟩ = ⟨aS i,haR i⟩ :=
      Subtype.ext ((hFL (bL i)).trans (hgmatch i))
    rw [← he,e.symm_apply_apply]
  have hp : MapCutsExact p e.symm δ := by
    intro x β hβ
    have hv : F (e.symm x) = (x:G) := congrArg Subtype.val (e.apply_symm_apply x)
    have hh := hFp (e.symm x) β hβ
    rw [hv] at hh
    exact hh.symm
  have hodd := terminal_one_odd_comparison G (G ⧸ T) p hG hQ rG rQ F.range D e.symm γ lG lQ
    hRank hp (0+k) aS bU haR haenum hcompat hbf
  have hd (i) : d i ∈ D := AddSubgroup.subset_closure ⟨i,rfl⟩
  let t : Fin (0+m) → F.range := append (fun i : Fin 0 => Fin.elim0 i) (fun i => e ⟨d i,hd i⟩)
  have hl : (fun i => (e.symm (t i):G ⧸ T)) = append (fun i : Fin 0 => Fin.elim0 i) d := by
    funext i
    induction i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i => simp only [t,append,Fin.addCases_right,AddEquiv.symm_apply_apply]
  have hr : (fun i => (t i:G)) = append (fun i : Fin 0 => Fin.elim0 i) (fun i => F ⟨d i,hd i⟩) := by
    funext i
    induction i using Fin.addCases with
    | left i => exact Fin.elim0 i
    | right i => simp only [t,append,Fin.addCases_right]; rfl
  have hh := hodd (0+m) t
  change BackAndForth (2*γ+1) (fun i => (e.symm (t i):G ⧸ T)) (fun i => (t i:G)) at hh
  rw [hl,hr] at hh
  exact ⟨fun i => F ⟨d i,hd i⟩,hh⟩
end LogicLineages.ModelsAlgebra.PGroups

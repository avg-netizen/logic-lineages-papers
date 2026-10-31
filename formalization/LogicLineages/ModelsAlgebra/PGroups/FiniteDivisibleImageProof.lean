module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteDivisibleImageTargets
public import LogicLineages.ModelsAlgebra.PGroups.FinitePrueferEmbeddingProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferFiniteSocleProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem finite_divisible_image : Targets.finiteDivisibleImage := by
  classical
  intro p _ D _ hp hD S _
  have hS : ∀ x : S, ∃ k : ℕ, p^k • x = 0 := by
    intro x
    obtain ⟨k,hk⟩ := hp x
    exact ⟨k,Subtype.ext hk⟩
  obtain ⟨n,i,hi⟩ := finite_pruefer_embedding p S hS
  have hP : GroupDivisible (Fin n → PrueferModel p) := by
    intro k hk x
    choose y hy using fun j => (genuine_pruefer_model p).2.1 k hk (x j)
    exact ⟨y,funext hy⟩
  obtain ⟨f,hf⟩ := divisible_hom_extension D (Fin n → PrueferModel p) hP S i
  have hinj : Function.Injective (f.comp S.subtype) := by
    intro x y h
    apply hi
    rw [←hf x,←hf y]
    exact h
  have hd : GroupDivisible f.range := by
    intro k hk x
    obtain ⟨a,ha⟩ := x.property
    obtain ⟨b,hb⟩ := hD k hk a
    refine ⟨⟨f b,⟨b,rfl⟩⟩,Subtype.ext ?_⟩
    change k • f b = (x:Fin n → PrueferModel p)
    rw [←map_nsmul,hb,ha]
  have hfin : Finite (pSocle p (⊤ : AddSubgroup f.range)) := by
    letI := finite_pruefer_power_socle p n
    let j : pSocle p (⊤ : AddSubgroup f.range) →
        pSocle p (⊤ : AddSubgroup (Fin n → PrueferModel p)) :=
      fun x => ⟨(x:f.range),AddSubgroup.mem_top _,
        congrArg (fun z : f.range => (z:Fin n → PrueferModel p)) x.property.2⟩
    apply Finite.of_injective j
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pSocle p (⊤ : AddSubgroup (Fin n → PrueferModel p)) =>
      (z:Fin n → PrueferModel p)) h
  exact ⟨n,f,hinj,hd,hfin,⟨QuotientAddGroup.quotientKerEquivRange f⟩⟩
end LogicLineages.ModelsAlgebra.PGroups

module
public import LogicLineages.ModelsAlgebra.PGroups.StabilizationSyntaxTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth

theorem stabilization_sentence_exact : Targets.stabilizationSentenceExact := by
  intro p N
  constructor
  · exact Complexity.pi two_ne_zero {0} (fun _=>1) (fun _=>stabilizationRoot p N)
      (fun _=>1) (fun _=>one_lt_two) (fun _=>
        Complexity.sigma one_ne_zero {0} (fun _=>1) _ (fun _=>0)
          (fun _=>zero_lt_one) (fun _=>Complexity.qf .pi _))
  · intro G _
    have hroot (d z:Fin 1→G) :
        (QF.equal
          (multipleTerm (p^N) (.var (Fin.castAdd 1 (Fin.natAdd 0 (0:Fin 1)))))
          (multipleTerm (p^(N+1)) (.var (Fin.natAdd (0+1) (0:Fin 1))))).Realize
            (append (append (Fin.elim0:Fin 0→G) d) z) ↔ p^N • d 0 = p^(N+1) • z 0 := by
      simp only [QF.Realize,multiple_term_evaluation G ((0+1)+1),GroupTerm.eval,append,Fin.addCases_left,Fin.addCases_right]
    have he : (stabilizationSentence p N).Realize (Fin.elim0:Fin 0→G) ↔
        ∀ x:G,∃y:G,p^N • x=p^(N+1) • y := by
      change (∀i:({0}:Set ℕ),∀d:Fin 1→G,∃k:({0}:Set ℕ),∃z:Fin 1→G,_ )↔_
      constructor
      · intro h x
        obtain ⟨_,z,hz⟩ := h ⟨0,by simp⟩ (fun _=>x)
        exact ⟨z 0,(hroot _ _).mp hz⟩
      · intro h _ d
        obtain ⟨y,hy⟩ := h (d 0)
        refine ⟨⟨0,by simp⟩,(fun _=>y),?_⟩
        simpa only [Formula.Realize] using (hroot d (fun _=>y)).mpr hy
    rw [he]
    change _ ↔ (transfiniteFiltration p (N:Ordinal):AddSubgroup G)=transfiniteFiltration p ((N:Ordinal)+1)
    rw [show (N:Ordinal)+1=((N+1:ℕ):Ordinal) by simp,finite_ordinal_filtration,finite_ordinal_filtration]
    rw [finite_filtration_multiple_image,finite_filtration_multiple_image]
    constructor
    · intro h
      apply le_antisymm
      · rintro x ⟨y,rfl⟩
        obtain ⟨z,hz⟩ := h y
        exact ⟨z,hz.symm⟩
      · rintro x ⟨y,rfl⟩
        refine ⟨p • y,?_⟩
        simp only [nsmulAddMonoidHom_apply,pow_succ',mul_nsmul]
    · intro h x
      have hx : p^N • x∈multipleImage G (p^N) := ⟨x,rfl⟩
      rw [h] at hx
      obtain ⟨y,hy⟩ := hx
      exact ⟨y,hy.symm⟩
end LogicLineages.ModelsAlgebra.PGroups

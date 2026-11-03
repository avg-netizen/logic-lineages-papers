module
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationPartialProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportAssignmentProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Proof
open SourceFreeOccurrences AdmissibleAssignment AssignmentSupport

theorem application_annotation {k Γ n} (p : AdmissibleSum.Policy)
    (F : Variable Γ (Ty.curriedGround (k+1)))
    (t : OriginalTerm Γ (Ty.curriedGround (n+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level) (a : OrdinalVector Γ 0)
    (hu : assignment p t = some u) (hq : Annotated p F (u 0)) (ha : Annotated p F (a 0)) :
    Annotated p F (application (σ := .ground) (τ := Ty.curriedGround n) p u a 0) := by
  change Annotated p F (.collapse
    (ordinalBoxPositive 0 (ordinalVectorAt u) (ordinalVectorAt a) 1) (.add (u 0) (a 0)))
  have he : ordinalBoxPositive 0 (ordinalVectorAt u) (ordinalVectorAt a) 1 =
      u (UnaryCarrier.headIndex n) := by
    rw [ordinalBoxPositive]
    split
    · omega
    · have h1 : 1 < (Ty.curriedGround (n+1)).level+1 := (UnaryCarrier.headIndex n).isLt
      unfold ordinalVectorAt
      rw [dif_pos h1]
      rfl
  rw [he]
  refine Annotated.collapse ⟨n,t,u,hu,rfl⟩ ?_ (Annotated.add hq ha)
  intro hx
  have hs := AssignmentSupport.Proof.assignment_support p t u hu
  have hqname := (hs.2 ⟨Ty.curriedGround (k+1),F⟩).mpr
    (hs.1 (UnaryCarrier.headIndex n) _ hx)
  change _ ∈ names (.add (u 0) (a 0))
  rw [AssignmentSupport.Proof.names_add, List.mem_append]
  exact Or.inl hqname

theorem abstraction_annotation {k Γ m} (p : AdmissibleSum.Policy)
    (F : Variable Γ (Ty.curriedGround (k+1)))
    (h : OrdinalVector (.ground :: Γ) m)
    (v : OrdinalVector Γ (max (Ty.ground.level+1) m))
    (hq : Annotated p (.there F) (h 0)) (hv : abstraction p h = some v) : Annotated p F (v 0) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  change Annotated p F (.add
    (repeated p .scalarRepeat (2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum)
      (ps 0 0)) (ordinalHeadClosure (h 0)))
  apply Annotated.add
  · apply annotated_repeated
    exact groundPartialTransport k Γ F p (h 0) (ps 0) hq
      (AssignmentSupport.Proof.collect_success _ _ _ hps 0)
  · exact headClosureTransport k Γ F p (h 0) hq

theorem actualSourceAnnotation : Targets.ActualSourceAnnotation := by
  intro k Γ F n p e
  induction e with
  | tracked => exact ⟨_,rfl,Annotated.tracked⟩
  | ground x =>
    refine ⟨_,rfl,Annotated.free ?_⟩
    intro hx
    change (⟨Ty.curriedGround (k+1),_⟩ : PackedVariable _) ∈ [⟨Ty.ground,x⟩] at hx
    have ht := congrArg Sigma.fst (List.mem_singleton.mp hx)
    simp only [Ty.curriedGround] at ht
    cases ht
  | free t hf =>
    obtain ⟨u,hu,_⟩ := actualAdmissibleAssignmentGenerated _ _ p t
    refine ⟨u,hu,Annotated.free ?_⟩
    intro hx
    exact hf ((AssignmentSupport.Proof.assignment_support p t u hu).2 _ |>.mp hx)
  | app f a ihf iha =>
    obtain ⟨uf,hf,hqf⟩ := ihf
    obtain ⟨ua,ha,hqa⟩ := iha
    refine ⟨application p uf ua,?_,application_annotation p _ (TrackedSource.erase f) uf ua hf hqf hqa⟩
    change (assignment p (TrackedSource.erase f)).bind (fun vf =>
      (assignment p (TrackedSource.erase a)).bind (fun va => some (application p vf va))) = _
    rw [hf]
    dsimp only [Option.bind]
    rw [ha]
  | @lam Γ F n body ih =>
    obtain ⟨h,hh,hq⟩ := ih
    obtain ⟨v,hv,_⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround (n+1)) p
      (TrackedSource.erase (.lam body))
    refine ⟨v,hv,abstraction_annotation p F h v hq ?_⟩
    change (assignment p (TrackedSource.erase body)).bind (fun w => abstraction p w) = some v at hv
    rw [hh] at hv
    exact hv
end LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Proof

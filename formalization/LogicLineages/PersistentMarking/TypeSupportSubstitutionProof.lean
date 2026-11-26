import LogicLineages.PersistentMarking.TypeSupportFoundationProof
namespace LogicLineages.PersistentMarking.TypeSupportSubstitutionProof
open Spine NameBridge TypeSupport TypeSupportFoundationProof

mutual
 def images (θ : FreeMap) : Expr → List Ty
  | .free σ x => support (θ σ x)
  | .bound _ _ => []
  | .lam _ q => images θ q
  | .head _ qs => imagesArgs θ qs
  | .marked _ _ qs es => imagesArgs θ qs ++ imagesArgs θ es
 def imagesArgs (θ : FreeMap) : Args → List Ty
  | .nil => []
  | .cons q qs => images θ q ++ imagesArgs θ qs
end

mutual
 theorem imagesExact (θ : FreeMap) (q : Expr) (ρ : Ty) : ρ ∈ images θ q ↔ ImageSupport θ q ρ := by
  cases q with
  | free σ x => simp [images,ImageSupport,freeOccurs,Prod.mk.injEq,and_assoc]
  | bound σ i => simp [images,ImageSupport,freeOccurs]
  | lam σ q => exact imagesExact θ q ρ
  | head f qs => exact imagesArgsExact θ qs ρ
  | marked f τ qs es =>
    simp only [images,List.mem_append,imagesArgsExact θ qs ρ,imagesArgsExact θ es ρ,ImageSupport,freeOccurs,Bool.or_eq_true]
    simp only [or_and_right,exists_or]
 termination_by sizeOf q
 theorem imagesArgsExact (θ : FreeMap) (qs : Args) (ρ : Ty) :
    ρ ∈ imagesArgs θ qs ↔ ∃ σ x, freeOccursArgs (σ,x) qs = true ∧ ρ ∈ support (θ σ x) := by
  cases qs with
  | nil => simp [imagesArgs,freeOccursArgs]
  | cons q qs =>
    simp only [imagesArgs,List.mem_append,imagesExact θ q ρ,imagesArgsExact θ qs ρ,ImageSupport,freeOccursArgs,Bool.or_eq_true]
    simp only [or_and_right,exists_or]
 termination_by sizeOf qs
end

mutual
 theorem exactSupport (θ : FreeMap) (ht : ∀ σ x, (θ σ x).type = σ) (d : Nat) (q : Expr) (ρ : Ty) :
    ρ ∈ support (freeSub θ d q) ↔ ρ ∈ support q ∨ ρ ∈ images θ q := by
  cases q with
  | free σ x =>
    simp only [freeSub,shiftSupport,support,images]
    constructor
    · exact Or.inr
    · intro h
      rcases h with h | h
      · exact rootSupport (θ σ x) ρ ((ht σ x).symm ▸ h)
      · exact h
  | bound σ i => simp [freeSub,support,images]
  | lam σ q =>
    simp only [freeSub,support,images,FreeCallProof.annotation θ ht,List.mem_append,exactSupport θ ht (d+1) q ρ]
    simp only [or_assoc]
  | head f qs =>
    simp only [freeSub,support,images,List.mem_append,exactArgsSupport θ ht d qs ρ]
    simp only [or_assoc]
  | marked f τ qs es =>
    simp only [freeSub,support,images,List.mem_append,exactArgsSupport θ ht d qs ρ,exactArgsSupport θ ht d es ρ]
    simp only [or_assoc,or_left_comm,or_comm]
 termination_by sizeOf q
 theorem exactArgsSupport (θ : FreeMap) (ht : ∀ σ x, (θ σ x).type = σ) (d : Nat) (qs : Args) (ρ : Ty) :
    ρ ∈ supportArgs (freeSubArgs θ d qs) ↔ ρ ∈ supportArgs qs ∨ ρ ∈ imagesArgs θ qs := by
  cases qs with
  | nil => simp [freeSubArgs,supportArgs,imagesArgs]
  | cons q qs =>
    simp only [freeSubArgs,supportArgs,imagesArgs,List.mem_append,exactSupport θ ht d q ρ,exactArgsSupport θ ht d qs ρ]
    simp only [or_assoc,or_left_comm,or_comm]
 termination_by sizeOf qs
end

theorem exactSubstitution : TypeSupportTargets.ExactSubstitution := by
  intro S q τ θ _ _ ht ρ
  have htype : ∀ σ x, (θ σ x).type = σ := fun σ x => SpineShiftProof.annotationExact _ _ _ (ht σ x).1.1
  exact (exactSupport θ htype 0 q ρ).trans (or_congr Iff.rfl (imagesExact θ q ρ))
end LogicLineages.PersistentMarking.TypeSupportSubstitutionProof

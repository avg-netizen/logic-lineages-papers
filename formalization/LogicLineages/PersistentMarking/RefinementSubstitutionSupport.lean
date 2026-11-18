import LogicLineages.PersistentMarking.RefinementTransitivityProof
import LogicLineages.PersistentMarking.FreeCallProof
namespace LogicLineages.PersistentMarking.RefinementSubstitutionSupport
open Spine NameBridge OpeningFoundationProof

theorem endpoints {S : Signature} {q s : Expr} (h : RefinementTree S q s) :
    PaperTerm S q q.type ∧ PaperTerm S s s.type := by
  cases h with
  | var => exact ⟨⟨.free,True.intro⟩,⟨.free,True.intro⟩⟩
  | abs hp hs _ _ _ =>
    have hq := SpineShiftProof.annotationExact _ _ _ hp.1
    have hs' := SpineShiftProof.annotationExact _ _ _ hs.1
    exact ⟨hq.symm ▸ hp,hs'.symm ▸ hs⟩
  | head hp hs _ => exact ⟨hp,hs⟩
  | marked hp hs _ _ => exact ⟨hp,hs⟩

mutual
 theorem shiftValid (S : Signature) (a d : Nat) (q : Expr) (h : Valid S q) : Valid S (shift a d q) := by
  cases q with
  | free σ x => trivial
  | bound σ i => trivial
  | lam σ q => exact shiftValid S a (d+1) q h
  | head f qs => exact ⟨h.1,shiftValidArgs S a d qs h.2⟩
  | marked f τ qs es => exact ⟨h.1,shiftValidArgs S a d qs h.2.1,shiftValidArgs S a d es h.2.2⟩
 termination_by sizeOf q
 theorem shiftValidArgs (S : Signature) (a d : Nat) (qs : Args) (h : ValidArgs S qs) : ValidArgs S (shiftArgs a d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨shiftValid S a d q h.1,shiftValidArgs S a d qs h.2⟩
 termination_by sizeOf qs
end

mutual
 theorem subValid (S : Signature) (θ : FreeMap) (hv : ∀ σ x, Valid S (θ σ x))
    (d : Nat) (q : Expr) (h : Valid S q) : Valid S (freeSub θ d q) := by
  cases q with
  | free σ x => exact shiftValid S d 0 (θ σ x) (hv σ x)
  | bound σ i => trivial
  | lam σ q => exact subValid S θ hv (d+1) q h
  | head f qs => exact ⟨h.1,subValidArgs S θ hv d qs h.2⟩
  | marked f τ qs es => exact ⟨h.1,subValidArgs S θ hv d qs h.2.1,subValidArgs S θ hv d es h.2.2⟩
 termination_by sizeOf q
 theorem subValidArgs (S : Signature) (θ : FreeMap) (hv : ∀ σ x, Valid S (θ σ x))
    (d : Nat) (qs : Args) (h : ValidArgs S qs) : ValidArgs S (freeSubArgs θ d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨subValid S θ hv d q h.1,subValidArgs S θ hv d qs h.2⟩
 termination_by sizeOf qs
end

theorem subPaper (S : Signature) (θ : FreeMap) (ht : FreeMapTyped EmptyContext θ)
    (hv : ∀ σ x, Valid S (θ σ x)) (q : Expr) (τ : Ty) (h : PaperTerm S q τ) :
    PaperTerm S (freeSub θ 0 q) τ := ⟨FreeTypingProof.freeSubTyped _ _ ht _ _ h.1,subValid S θ hv 0 q h.2⟩

mutual
 theorem shiftOccurs (name : Name) (a d : Nat) (q : Expr) : freeOccurs name (shift a d q) = freeOccurs name q := by
  cases q with
  | free σ x => rfl
  | bound σ i => simp [shift,freeOccurs]
  | lam σ q => exact shiftOccurs name a (d+1) q
  | head f qs => exact shiftOccursArgs name a d qs
  | marked f τ qs es => simp only [shift,freeOccurs,shiftOccursArgs name a d qs,shiftOccursArgs name a d es]
 termination_by sizeOf q
 theorem shiftOccursArgs (name : Name) (a d : Nat) (qs : Args) : freeOccursArgs name (shiftArgs a d qs) = freeOccursArgs name qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,freeOccursArgs,shiftOccurs name a d q,shiftOccursArgs name a d qs]
 termination_by sizeOf qs
end

/- Only images of actually occurring free leaves contribute, not the infinite
map's unused values. -/
mutual
 def imageBound (θ : FreeMap) : Expr → Nat
   | .free σ x => maxFreeName (θ σ x)
   | .bound _ _ => 0
   | .lam _ q => imageBound θ q
   | .head _ qs => imageBoundArgs θ qs
   | .marked _ _ qs es => max (imageBoundArgs θ qs) (imageBoundArgs θ es)
 def imageBoundArgs (θ : FreeMap) : Args → Nat
   | .nil => 0
   | .cons q qs => max (imageBound θ q) (imageBoundArgs θ qs)
end

mutual
 theorem imageFresh (θ : FreeMap) (σ : Ty) (x d : Nat) (q : Expr) (h : imageBound θ q < x) :
    freeOccurs (σ,x) (freeSub θ d q) = false := by
  cases q with
  | free τ y => exact (shiftOccurs (σ,x) d 0 (θ τ y)).trans (aboveFresh σ x _ h)
  | bound τ i => rfl
  | lam τ q => exact imageFresh θ σ x (d+1) q h
  | head f qs => exact imageFreshArgs θ σ x d qs h
  | marked f τ qs es =>
    have hb : imageBoundArgs θ qs < x := by change max _ _ < x at h; omega
    have he : imageBoundArgs θ es < x := by change max _ _ < x at h; omega
    simp only [freeSub,freeOccurs,imageFreshArgs θ σ x d qs hb,imageFreshArgs θ σ x d es he,Bool.false_or]
 termination_by sizeOf q
 theorem imageFreshArgs (θ : FreeMap) (σ : Ty) (x d : Nat) (qs : Args) (h : imageBoundArgs θ qs < x) :
    freeOccursArgs (σ,x) (freeSubArgs θ d qs) = false := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hq : imageBound θ q < x := by change max _ _ < x at h; omega
    have hqs : imageBoundArgs θ qs < x := by change max _ _ < x at h; omega
    simp only [freeSubArgs,freeOccursArgs,imageFresh θ σ x d q hq,imageFreshArgs θ σ x d qs hqs,Bool.false_or]
 termination_by sizeOf qs
end

def mask (θ : FreeMap) (σ : Ty) (x : Nat) : FreeMap := fun τ y => if (τ,y)=(σ,x) then .free τ y else θ τ y

theorem maskTyped (θ : FreeMap) (σ : Ty) (x : Nat) (h : FreeMapTyped EmptyContext θ) : FreeMapTyped EmptyContext (mask θ σ x) := by
  intro τ y
  unfold mask
  split
  · exact .free
  · exact h τ y

theorem maskRefines (S : Signature) (γ δ : FreeMap) (σ : Ty) (x : Nat)
    (h : ∀ τ y, Refines S (γ τ y) (δ τ y)) :
    ∀ τ y, Refines S (mask γ σ x τ y) (mask δ σ x τ y) := by
  intro τ y
  by_cases he : (τ,y)=(σ,x)
  · simp only [mask,he,if_true]; exact ⟨.var⟩
  · simpa only [mask,he,if_false] using h τ y

mutual
 theorem maskedAbsent (θ : FreeMap) (σ : Ty) (x d : Nat) (q : Expr) (h : freeOccurs (σ,x) q = false) :
    freeSub (mask θ σ x) d q = freeSub θ d q := by
  cases q with
  | free τ y =>
    have hn : (σ,x) ≠ (τ,y) := by simpa only [freeOccurs,decide_eq_false_iff_not] using h
    have hn' : (τ,y) ≠ (σ,x) := fun he => hn he.symm
    simp only [freeSub,mask,hn',if_false]
  | bound τ i => rfl
  | lam τ q => exact congrArg (Expr.lam τ) (maskedAbsent θ σ x (d+1) q h)
  | head f qs => exact congrArg (Expr.head f) (maskedAbsentArgs θ σ x d qs h)
  | marked f τ qs es =>
    have hh : freeOccursArgs (σ,x) qs = false ∧ freeOccursArgs (σ,x) es = false := by simpa only [freeOccurs,Bool.or_eq_false_iff] using h
    change Expr.marked f τ _ _ = Expr.marked f τ _ _
    exact congr (congrArg (Expr.marked f τ) (maskedAbsentArgs θ σ x d qs hh.1)) (maskedAbsentArgs θ σ x d es hh.2)
 termination_by sizeOf q
 theorem maskedAbsentArgs (θ : FreeMap) (σ : Ty) (x d : Nat) (qs : Args) (h : freeOccursArgs (σ,x) qs = false) :
    freeSubArgs (mask θ σ x) d qs = freeSubArgs θ d qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hh : freeOccurs (σ,x) q = false ∧ freeOccursArgs (σ,x) qs = false := by simpa only [freeOccursArgs,Bool.or_eq_false_iff] using h
    change Args.cons _ _ = Args.cons _ _
    exact congr (congrArg Args.cons (maskedAbsent θ σ x d q hh.1)) (maskedAbsentArgs θ σ x d qs hh.2)
 termination_by sizeOf qs
end

theorem maskedOpening (θ : FreeMap) (σ : Ty) (x : Nat) (q : Expr) (h : freeOccurs (σ,x) q = false) :
    freeSub (mask θ σ x) 0 (openBody σ x q) = openBody σ x (freeSub θ 1 q) := by
  have hc := FreeCompositionProof.composition (mask θ σ x) (.cons (.free σ x) .nil) 0 q
  simpa only [openBody,freeSubArgs,freeSub,mask,ite_true,shift,Args.length,Nat.zero_add,Nat.add_zero,maskedAbsent θ σ x 1 q h] using hc

end LogicLineages.PersistentMarking.RefinementSubstitutionSupport

import LogicLineages.PersistentMarking.TypeSupportTargets
import LogicLineages.PersistentMarking.FreeCallProof
namespace LogicLineages.PersistentMarking.TypeSupportFoundationProof
open Spine NameBridge StructuralContext TypeSupport

theorem rootSupport : TypeSupportTargets.RootSupport := by
  intro q ρ h
  cases q with
  | free σ x => exact h
  | bound σ i => exact h
  | lam σ body => simp only [support,List.mem_append]; exact Or.inl (Or.inl h)
  | head f base => simp only [support,List.mem_append]; exact Or.inl h
  | marked f τ base extras => simp only [support,List.mem_append]; exact Or.inl (Or.inl h)

mutual
 theorem shiftSupport (k d : Nat) (q : Expr) : support (shift k d q) = support q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ q => simp only [shift,support,SubstitutionProof.shiftType,shiftSupport k (d+1) q]
  | head f qs => simp only [shift,support,shiftSupportArgs k d qs]
  | marked f τ qs es => simp only [shift,support,shiftSupportArgs k d qs,shiftSupportArgs k d es]
 termination_by sizeOf q
 theorem shiftSupportArgs (k d : Nat) (qs : Args) : supportArgs (shiftArgs k d qs) = supportArgs qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,supportArgs,shiftSupport k d q,shiftSupportArgs k d qs]
 termination_by sizeOf qs
end

theorem closingAnnotation (name : Name) : ∀ σ x, (closingMap name σ x).type = σ := by
  intro σ x
  by_cases he : (σ,x) = name <;> simp [closingMap,he,Expr.type]

mutual
 theorem closing (name : Name) (d : Nat) (q : Expr) : support (freeSub (closingMap name) d q) = support q := by
  cases q with
  | free σ x =>
    by_cases he : (σ,x) = name <;> simp [freeSub,closingMap,he,shift,support]
  | bound σ i => rfl
  | lam σ q =>
    simp only [freeSub,support,FreeCallProof.annotation _ (closingAnnotation name),closing name (d+1) q]
  | head f qs => simp only [freeSub,support,closingArgs name d qs]
  | marked f τ qs es => simp only [freeSub,support,closingArgs name d qs,closingArgs name d es]
 termination_by sizeOf q
 theorem closingArgs (name : Name) (d : Nat) (qs : Args) :
    supportArgs (freeSubArgs (closingMap name) d qs) = supportArgs qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [freeSubArgs,supportArgs,closing name d q,closingArgs name d qs]
 termination_by sizeOf qs
end

theorem closingSupport : TypeSupportTargets.ClosingSupport := fun name q => closing name 0 q

theorem encodeAnnotation (env : List Name) (q : Term) : (encode env q).type = q.type := by
  cases q with
  | var σ x => cases hl : nameLookup env (σ,x) <;> simp [encode,hl,Expr.type,Term.type]
  | lam σ x q => simp only [encode,Expr.type,Term.type,encodeAnnotation ((σ,x)::env) q]
  | head f qs => rfl
  | marked f τ qs es => rfl
termination_by sizeOf q

mutual
 theorem encodingSupport (env : List Name) (q : Term) : support (encode env q) = namedSupport q := by
  cases q with
  | var σ x => cases hl : nameLookup env (σ,x) <;> simp [encode,hl,support,namedSupport]
  | lam σ x q => simp only [encode,support,namedSupport,encodeAnnotation,encodingSupport ((σ,x)::env) q]
  | head f qs => simp only [encode,support,namedSupport,encodingSupportArgs env qs]
  | marked f τ qs es => simp only [encode,support,namedSupport,encodingSupportArgs env qs,encodingSupportArgs env es]
 termination_by sizeOf q
 theorem encodingSupportArgs (env : List Name) (qs : List Term) : supportArgs (encodeArgs env qs) = namedSupportArgs qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [encodeArgs,supportArgs,namedSupportArgs,encodingSupport env q,encodingSupportArgs env qs]
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.TypeSupportFoundationProof

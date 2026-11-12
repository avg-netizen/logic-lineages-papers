module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundProof
open Source NumberedAuxiliaryCoding OriginalStructuralNodeSize OriginalRawSyntaxTransport
open OriginalHereditaryWorkBound

theorem childrenLength {Symbol : Type} (Gamma : List Ty) (code : Code Symbol) :
    (children Gamma code).length ≤ 2 := by
  cases code <;> simp [children]

theorem childWeight {Symbol : Type} (Gamma : List Ty) (code : Code Symbol)
    (t : State Symbol) (ht : t ∈ children Gamma code) :
    weight t < weight ⟨Gamma,code⟩ := by
  cases code <;> simp only [children,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ht
  all_goals first
    | contradiction
    | (rcases ht with rfl | rfl <;> simp only [weight,nodeCount,List.length_cons] <;> omega)
    | (cases ht; simp only [weight,nodeCount,List.length_cons]; omega)

theorem deletionsLength {Symbol : Type} (code : Code Symbol) (prefix tail : List Ty) :
    (deletionsFrom code prefix tail).length = tail.length := by
  induction tail generalizing prefix with
  | nil => rfl
  | cons sigma tail ih => simp only [deletionsFrom,List.length_cons,ih]

theorem deletionWeight {Symbol : Type} (code : Code Symbol) (prefix tail : List Ty)
    (t : State Symbol) (ht : t ∈ deletionsFrom code prefix tail) :
    weight t + 1 = (prefix ++ tail).length + 2 * nodeCount code := by
  induction tail generalizing prefix with
  | nil => cases ht
  | cons sigma tail ih =>
    rcases List.mem_cons.mp ht with he | ht
    · cases he
      simp only [weight,OriginalStructuralNodeSizeNativeSyntaxProof.eraseInvariant,
        List.length_append,List.length_cons]
      omega
    · have h := ih (prefix ++ [sigma]) ht
      simp only [List.length_append,List.length_singleton,List.length_cons] at h ⊢
      omega

theorem successorBounds : OriginalHereditaryWorkBoundTargets.SuccessorBounds := by
  intro Symbol s
  constructor
  · have hc := childrenLength s.context s.code
    simp only [successors,List.length_append,deletionsLength]
    unfold weight
    omega
  · intro t ht
    rcases List.mem_append.mp ht with hc | hd
    · exact childWeight s.context s.code t hc
    · have h := deletionWeight s.code [] s.context t hd
      simp only [List.nil_append] at h
      change weight t < s.context.length + 2 * nodeCount s.code
      omega

theorem pathBound : OriginalHereditaryWorkBoundTargets.PathBound := by
  intro Symbol depth s t h
  induction h with
  | refl s => simp
  | @cons depth s t u ht h ih =>
    have hs := (successorBounds Symbol s).2 t ht
    omega

theorem sumMapBound {A : Type} (f : A → Nat) (xs : List A) (bound : Nat)
    (h : ∀ x ∈ xs, f x ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add hx ht

theorem visitsBound {Symbol : Type} (depth limit : Nat) (s : State Symbol)
    (hs : weight s ≤ limit) : visits depth s ≤ budget (limit+2) depth := by
  induction depth generalizing s with
  | zero => exact Nat.le_refl _
  | succ depth ih =>
    have hh := successorBounds Symbol s
    have hm : ∀ t ∈ successors s, visits depth t ≤ budget (limit+2) depth := by
      intro t ht
      exact ih t (Nat.le_trans (Nat.le_of_lt (hh.2 t ht)) hs)
    have hsum := sumMapBound (visits depth) (successors s) (budget (limit+2) depth) hm
    have hlen : (successors s).length ≤ limit+2 := Nat.le_trans hh.1 (Nat.add_le_add_right hs 2)
    have hprod := Nat.mul_le_mul_right (budget (limit+2) depth) hlen
    exact Nat.add_le_add_left (Nat.le_trans hsum hprod) 1

theorem workBound : OriginalHereditaryWorkBoundTargets.WorkBound := by
  intro Symbol s
  exact visitsBound (weight s) (weight s) s (Nat.le_refl _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundProof

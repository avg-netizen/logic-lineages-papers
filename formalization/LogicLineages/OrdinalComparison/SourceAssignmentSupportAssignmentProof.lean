module
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportPartialProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof
open SourceFreeOccurrences AdmissibleAssignment AdmissibleSum

theorem supported_add {Γ : List Ty} {S : List (PackedVariable Γ)} {a b : OrdinalExpression Γ}
    (ha : Supported S a) (hb : Supported S b) : Supported S (.add a b) := by
  intro x hx
  rw [names_add,List.mem_append] at hx
  exact hx.elim (ha x) (hb x)

theorem supported_emul {Γ : List Ty} {S : List (PackedVariable Γ)} {a b : OrdinalExpression Γ}
    (ha : Supported S a) (hb : Supported S b) : Supported S (.emul a b) := by
  intro x hx
  rw [names_emul,List.mem_append] at hx
  exact hx.elim (ha x) (hb x)

theorem supported_collapse {Γ : List Ty} {S : List (PackedVariable Γ)} {a b : OrdinalExpression Γ}
    (ha : Supported S a) (hb : Supported S b) : Supported S (.collapse a b) := by
  intro x hx
  rw [names_collapse,List.mem_append] at hx
  exact hx.elim (ha x) (hb x)

theorem supported_headClosure {Γ : List Ty} {σ : Ty} {S : List (PackedVariable (σ :: Γ))}
    {t : OrdinalExpression (σ :: Γ)} (ht : Supported S t) :
    Supported (S.filterMap dropBound) (ordinalHeadClosure t) := by
  intro x hx
  rw [exactHeadClosureNames Γ σ t] at hx
  obtain ⟨y,hy,he⟩ := List.mem_filterMap.mp hx
  exact List.mem_filterMap.mpr ⟨y,ht y hy,he⟩

theorem supported_filter_mono {Γ : List Ty} {σ : Ty} {S : List (PackedVariable (σ :: Γ))}
    {t : OrdinalExpression (σ :: Γ)} (ht : Supported S t) :
    ∀x∈(names t).filterMap dropBound,x∈S.filterMap dropBound := by
  intro x hx
  obtain ⟨y,hy,he⟩ := List.mem_filterMap.mp hx
  exact List.mem_filterMap.mpr ⟨y,ht y hy,he⟩

theorem vectorAt_supported {Γ : List Ty} {m : Nat} {S : List (PackedVariable Γ)}
    (v : OrdinalVector Γ m) (hv : ∀j,Supported S (v j)) (i : Nat) : Supported S (ordinalVectorAt v i) := by
  unfold ordinalVectorAt
  split_ifs
  · exact hv _
  · intro x hx; simp only [names_zero,List.not_mem_nil] at hx

theorem positive_supported {Γ : List Ty} (S : List (PackedVariable Γ)) (n : Nat)
    (f g : Nat→OrdinalExpression Γ) (hf : ∀i,Supported S (f i)) (hg : ∀i,Supported S (g i))
    (i : Nat) : Supported S (ordinalBoxPositive n f g i) := by
  rw [ordinalBoxPositive]
  split_ifs with hi
  · exact supported_emul (positive_supported S n f g hf hg (i+1)) (supported_add (hf i) (hg i))
  · exact hf i
termination_by n+1-i
decreasing_by omega

theorem boxTail_supported {Γ : List Ty} {S : List (PackedVariable Γ)} (p : Policy) (n : Nat)
    (f g : OrdinalExpression Γ) (hf : Supported S f) (hg : Supported S g) : Supported S (boxTail p n f g) := by
  unfold boxTail
  split_ifs
  · exact supported_add hf hg
  · intro x hx
    rw [names_three_mem] at hx
    rcases hx with hx|hx|hx
    · exact hf x hx
    · exact hg x hx
    · exact supported_numeral p n x hx

theorem box_supported {Γ : List Ty} {m n : Nat} {S : List (PackedVariable Γ)} (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (hf : ∀j,Supported S (f j)) (hg : ∀j,Supported S (g j)) : ∀j,Supported S (box p f g j) := by
  intro j
  unfold box
  split_ifs
  · exact supported_collapse
      (positive_supported S n _ _ (vectorAt_supported f hf) (vectorAt_supported g hg) 1)
      (boxTail_supported p n _ _ (hf 0) (hg 0))
  · exact positive_supported S n _ _ (vectorAt_supported f hf) (vectorAt_supported g hg) j.val

theorem application_supported {Γ : List Ty} {σ τ : Ty} {S : List (PackedVariable Γ)} (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level)
    (hf : ∀j,Supported S (f j)) (hg : ∀j,Supported S (g j)) :
    ∀j,Supported S (application p f g j) := fun j=>box_supported p f g hf hg _

theorem boxTail_contains {Γ : List Ty} (p : Policy) (n : Nat) (f g : OrdinalExpression Γ)
    (x : PackedVariable Γ) (hx : x∈names f ∨ x∈names g) : x∈names (boxTail p n f g) := by
  unfold boxTail
  split_ifs
  · simpa only [names_add,List.mem_append] using hx
  · rw [names_three_mem]
    exact hx.elim Or.inl (fun h=>Or.inr (Or.inl h))

theorem application_scalar_contains {Γ : List Ty} {σ τ : Ty} (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level)
    (x : PackedVariable Γ) (hx : x∈names (f 0) ∨ x∈names (g 0)) :
    x∈names (application p f g 0) := by
  change x∈names (.collapse _ (boxTail p σ.level (f 0) (g 0)))
  rw [names_collapse,List.mem_append]
  exact Or.inr (boxTail_contains p _ _ _ x hx)

theorem collect_success {α : Type} (n : Nat) (f : Fin n→Option α)
    (v : Fin n→α) (hv : collect n f=some v) : ∀i,f i=some (v i) := by
  induction n with
  | zero => intro i;exact Fin.elim0 i
  | succ n ih =>
    have he : ∃a,f 0=some a ∧ ∃w,
        collect n (fun i=>f i.succ)=some w ∧ Fin.cases a w=v := by
      simpa only [collect,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using hv
    obtain ⟨a,ha,w,hw,rfl⟩ := he
    intro i
    exact Fin.cases ha (ih _ w hw) i

theorem abstraction_supported {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ :: Γ) m) (v : OrdinalVector Γ (max (σ.level+1) m))
    (S : List (PackedVariable (σ :: Γ))) (hh : ∀i,Supported S (h i))
    (hv : abstraction p h=some v) : ∀j,Supported (S.filterMap dropBound) (v j) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  have hpartial : ∀i j,Supported (S.filterMap dropBound) (ps i j) := by
    intro i j
    exact supported_mono (supported_filter_mono (hh i))
      (actualPartialSupport Γ σ p i.val (h i) (ps i) (collect_success _ _ _ hps i) j)
  intro j
  have hd : Supported (S.filterMap dropBound)
      (if j.val=0 then repeated p .scalarRepeat
        (2^(σ.level+1)*((List.ofFn h).map ordinalPartialSize).sum) (ps 0 0)
       else if hj : j.val<σ.level+2 then
         expand (p.shape .positiveAbstraction m) (fun i=>ps i ⟨j.val,hj⟩)
       else ordinalHeadClosure (h ⟨j.val,by have := j.isLt;omega⟩)) := by
    split
    · exact supported_repeated p .scalarRepeat _ _ (hpartial 0 0)
    · split
      · exact supported_expand _ _ (fun i=>hpartial i _)
      · exact supported_headClosure (hh _)
  by_cases hm : j.val<m+1
  · simpa only [dif_pos hm] using supported_add hd (supported_headClosure (hh ⟨j.val,hm⟩))
  · simpa only [dif_neg hm] using hd

theorem abstraction_scalar_contains {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ :: Γ) m) (v : OrdinalVector Γ (max (σ.level+1) m))
    (hv : abstraction p h=some v) (x : PackedVariable Γ)
    (hx : x∈names (ordinalHeadClosure (h 0))) : x∈names (v 0) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  change x∈names (.add _ (ordinalHeadClosure (h 0)))
  rw [names_add,List.mem_append]
  exact Or.inr hx

theorem assignment_support {Γ : List Ty} {τ : Ty} (p : Policy) (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : assignment p t=some v) :
    (∀j,Supported (freeOccurrences t) (v j)) ∧
      ∀x : PackedVariable Γ,x∈names (v 0) ↔ x∈freeOccurrences t := by
  induction t with
  | var x =>
    have he : (fun i=>.var ⟨_,x,i⟩)=v := Option.some.inj hv
    subst v
    constructor
    · intro j y hy
      simpa only [names_var,freeOccurrences,componentName] using hy
    · intro y
      rfl
  | zeroC | succC | caseC _ =>
    have he : (fun _=>.one)=v := Option.some.inj hv
    subst v
    constructor
    · intro j x hx;simp only [names_one,List.not_mem_nil] at hx
    · intro x;rfl
  | @recC Γ σ =>
    have he : (fun i : Fin (σ.recType.level+1)=>if i.val=0 then numeral p 2
      else if i.val=σ.level+2 then .omega else .one)=v := Option.some.inj hv
    subst v
    have hs : ∀j : Fin (σ.recType.level+1),Supported ([] : List (PackedVariable Γ))
        (if j.val=0 then numeral p 2 else if j.val=σ.level+2 then .omega else .one) := by
      intro j
      split_ifs
      · exact supported_numeral p 2
      · intro x hx;simp only [names_omega,List.not_mem_nil] at hx
      · intro x hx;simp only [names_one,List.not_mem_nil] at hx
    refine ⟨hs,?_⟩
    intro x
    constructor
    · exact hs 0 x
    · intro hx;cases hx
  | @app Γ σ τ f a ihf iha =>
    have he : ∃vf,assignment p f=some vf ∧ ∃va,assignment p a=some va ∧ application p vf va=v := by
      simpa only [assignment,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using hv
    obtain ⟨vf,hf,va,ha,rfl⟩ := he
    obtain ⟨hfs,hf0⟩ := ihf vf hf
    obtain ⟨has,ha0⟩ := iha va ha
    have hs := application_supported p vf va
      (fun j=>supported_mono (fun x hx=>List.mem_append_left _ hx) (hfs j))
      (fun j=>supported_mono (fun x hx=>List.mem_append_right _ hx) (has j))
    refine ⟨hs,?_⟩
    intro x
    constructor
    · exact hs 0 x
    · intro hx
      apply application_scalar_contains p vf va x
      rcases List.mem_append.mp hx with hx|hx
      · exact Or.inl ((hf0 x).mpr hx)
      · exact Or.inr ((ha0 x).mpr hx)
  | @lam Γ σ τ body ih =>
    have he : ∃h,assignment p body=some h ∧ abstraction p h=some v := by
      change (assignment p body).bind (fun h=>abstraction p h)=some v at hv
      exact Option.bind_eq_some_iff.mp hv
    obtain ⟨h,hb,ha⟩ := he
    obtain ⟨hh,hh0⟩ := ih h hb
    have hs := abstraction_supported p h v (freeOccurrences body) hh ha
    refine ⟨hs,?_⟩
    intro x
    constructor
    · exact hs 0 x
    · intro hx
      apply abstraction_scalar_contains p h v ha x
      rw [exactHeadClosureNames Γ σ (h 0)]
      obtain ⟨y,hy,he⟩ := List.mem_filterMap.mp hx
      exact List.mem_filterMap.mpr ⟨y,(hh0 y).mpr hy,he⟩
  | ranked s args ih => nomatch s

theorem fullActualAssignmentSupport : Targets.FullActualAssignmentSupport := by
  intro Γ τ p t
  obtain ⟨v,hv,hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  exact ⟨v,hv,assignment_support p t v hv⟩
end LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof

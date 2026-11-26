import LogicLineages.PersistentMarking.LiteralDerivationLocalityTargets
import LogicLineages.PersistentMarking.DecisionSourceBasicProof

namespace LogicLineages.PersistentMarking.LiteralWindowSupportProof
open Spine DecisionInventory TypeSupport

abbrev Covers (K : List Ty) (xs : List Ty) := ∀ ρ, ρ ∈ xs → ρ ∈ K
abbrev TermIn (K : List Ty) (q : Expr) := Covers K (auxiliarySupport q)
abbrev ArgsIn (K : List Ty) (xs : Spine.Args) := Covers K (auxiliaryArgs xs)

theorem empty {K : List Ty} : Covers K [] := fun _ h => False.elim (List.not_mem_nil h)

theorem left {K xs ys : List Ty} (h : Covers K (xs ++ ys)) : Covers K xs :=
  fun ρ hr => h ρ (List.mem_append_left _ hr)

theorem right {K xs ys : List Ty} (h : Covers K (xs ++ ys)) : Covers K ys :=
  fun ρ hr => h ρ (List.mem_append_right _ hr)

theorem join {K xs ys : List Ty} (h : Covers K xs) (g : Covers K ys) : Covers K (xs ++ ys) :=
  fun ρ hr => (List.mem_append.mp hr).elim (h ρ) (g ρ)

theorem argsJoin {K : List Ty} (xs ys : Spine.Args) (h : ArgsIn K xs) (g : ArgsIn K ys) :
    ArgsIn K (xs.append ys) := by
  cases xs with
  | nil => exact g
  | cons a rest => exact join (left h) (argsJoin rest ys (right h) g)
termination_by sizeOf xs

theorem selected {K : List Ty} {xs : Spine.Args} {i : Nat} {q : Expr}
    (h : At xs i q) : ArgsIn K xs → TermIn K q := by
  induction h with
  | here => exact left
  | there _ ih => exact fun h => ih (right h)

theorem removeParts {K : List Ty} {xs tail : Spine.Args} {q : Expr}
    (h : Remove xs q tail) : ArgsIn K xs → TermIn K q ∧ ArgsIn K tail := by
  induction h with
  | here => exact fun hg => ⟨left hg,right hg⟩
  | there _ ih =>
    intro hg
    obtain ⟨ha,ht⟩ := ih (right hg)
    exact ⟨ha,join (left hg) ht⟩

theorem splitParts {K : List Ty} {xs ys zs : Spine.Args} (h : Split xs ys zs) :
    ArgsIn K xs → ArgsIn K ys ∧ ArgsIn K zs := by
  induction h with
  | nil => exact fun hg => ⟨hg,hg⟩
  | left _ ih =>
    intro hg
    obtain ⟨hy,hz⟩ := ih (right hg)
    exact ⟨join (left hg) hy,hz⟩
  | right _ ih =>
    intro hg
    obtain ⟨hy,hz⟩ := ih (right hg)
    exact ⟨hy,join (left hg) hz⟩

theorem rootIn {K : List Ty} {q : Expr} (h : TermIn K q) : q.type ∈ K := by
  apply h
  cases q with
  | free σ x => exact DecisionSourceBasicProof.subtypeSelf σ
  | bound σ i => exact DecisionSourceBasicProof.subtypeSelf σ
  | lam σ q => exact List.mem_append_left _ (List.mem_append_left _ (DecisionSourceBasicProof.subtypeSelf _))
  | head f bs => exact List.mem_append_left _ (List.mem_append_left _ (DecisionSourceBasicProof.subtypeSelf _))
  | marked f τ bs es =>
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (DecisionSourceBasicProof.subtypeSelf _)))

theorem lamBody {K : List Ty} {σ : Ty} {q : Expr} (h : TermIn K (.lam σ q)) : TermIn K q :=
  right h

theorem lamDomain {K : List Ty} {σ : Ty} {q : Expr} (h : TermIn K (.lam σ q)) : Covers K (subtypes σ) :=
  right (left h)

theorem markedParts {K : List Ty} {f : Head} {τ : Ty} {bs es : Spine.Args}
    (h : TermIn K (.marked f τ bs es)) :
    Covers K (declaration f) ∧ Covers K (subtypes τ) ∧ ArgsIn K bs ∧ ArgsIn K es :=
  ⟨left (left (left h)),right (left (left h)),right (left h),right h⟩

theorem markedBuild {K : List Ty} {f : Head} {τ : Ty} {bs es : Spine.Args}
    (hd : Covers K (declaration f)) (hτ : Covers K (subtypes τ))
    (hb : ArgsIn K bs) (he : ArgsIn K es) : TermIn K (.marked f τ bs es) :=
  join (join (join hd hτ) hb) he

theorem arrowDomain {K : List Ty} {σ τ : Ty} (h : Covers K (subtypes (.arrow σ τ))) :
    Covers K (subtypes σ) :=
  fun ρ hρ => h ρ (List.mem_cons_of_mem _ (List.mem_append_left _ hρ))

theorem arrowResult {K : List Ty} {σ τ : Ty} (h : Covers K (subtypes (.arrow σ τ))) :
    Covers K (subtypes τ) :=
  fun ρ hρ => h ρ (List.mem_cons_of_mem _ (List.mem_append_right _ hρ))

end LogicLineages.PersistentMarking.LiteralWindowSupportProof

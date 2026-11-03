module
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof
open SourceFreeOccurrences AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

@[simp] theorem names_var {Γ} (c : OrdinalComponent Γ) : names (.var c) = [componentName c] := rfl
@[simp] theorem names_zero {Γ} : names (.zero : OrdinalExpression Γ) = [] := rfl
@[simp] theorem names_one {Γ} : names (.one : OrdinalExpression Γ) = [] := rfl
@[simp] theorem names_omega {Γ} : names (.omega : OrdinalExpression Γ) = [] := rfl
@[simp] theorem names_add {Γ} (a b : OrdinalExpression Γ) :
    names (.add a b) = names a ++ names b := List.map_append ..
@[simp] theorem names_emul {Γ} (a b : OrdinalExpression Γ) :
    names (.emul a b) = names a ++ names b := List.map_append ..
@[simp] theorem names_collapse {Γ} (a b : OrdinalExpression Γ) :
    names (.collapse a b) = names a ++ names b := List.map_append ..

theorem names_headClosure {Γ σ} (t : OrdinalExpression (σ :: Γ)) :
    names (ordinalHeadClosure t) = (names t).filterMap dropBound := by
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x <;> simp [ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
      names, ordinalExpressionVariables, componentName, dropBound]
  | zero | one | omega => rfl
  | add f g ihf ihg | emul f g ihf ihg | collapse f g ihf ihg =>
    simp only [ordinalHeadClosure, substitute] at ihf ihg ⊢
    simp only [names_add, names_emul, names_collapse, List.filterMap_append, ihf, ihg]

theorem exactHeadClosureNames : Targets.ExactHeadClosureNames := by
  intro Γ σ t
  exact names_headClosure t

theorem names_expand_mem {Γ n} (s : Shape n) (xs : Fin n → OrdinalExpression Γ)
    (x : PackedVariable Γ) : x ∈ names (expand s xs) ↔ ∃ i, x ∈ names (xs i) := by
  induction s with
  | leaf =>
    simp only [expand]
    constructor
    · exact fun h => ⟨0, h⟩
    · rintro ⟨i, hi⟩
      have : i = 0 := Fin.ext (by omega)
      simpa [this] using hi
  | @join n m a b iha ihb =>
    simp only [expand, names_add, List.mem_append, iha, ihb]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨Fin.castAdd m i, hi⟩
      · exact ⟨Fin.natAdd n i, hi⟩
    · rintro ⟨i, hi⟩
      by_cases h : i.val < n
      · left
        refine ⟨⟨i.val, h⟩, ?_⟩
        simpa only [show Fin.castAdd m (⟨i.val, h⟩ : Fin n) = i from Fin.ext rfl] using hi
      · right
        have hm : i.val - n < m := by have := i.isLt; omega
        refine ⟨⟨i.val - n, hm⟩, ?_⟩
        have he : Fin.natAdd n (⟨i.val - n, hm⟩ : Fin m) = i := Fin.ext (by simp; omega)
        simpa only [he] using hi

theorem supported_mono {Γ} {S T : List (PackedVariable Γ)} {t : OrdinalExpression Γ}
    (hST : ∀ x ∈ S, x ∈ T) (ht : Supported S t) : Supported T t :=
  fun x hx => hST x (ht x hx)

theorem supported_expand {Γ n} {S : List (PackedVariable Γ)}
    (s : Shape n) (xs : Fin n → OrdinalExpression Γ) (h : ∀ i, Supported S (xs i)) :
    Supported S (expand s xs) := by
  intro x hx
  obtain ⟨i, hi⟩ := (names_expand_mem s xs x).mp hx
  exact h i x hi

theorem names_three_mem {Γ} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) (x : PackedVariable Γ) :
    x ∈ names (AdmissiblePartial.three p site a b c) ↔
      x ∈ names a ∨ x ∈ names b ∨ x ∈ names c := by
  unfold AdmissiblePartial.three
  rw [names_expand_mem]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h0 h1
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · rintro (ha | hb | hc)
    · exact ⟨0, by simpa using ha⟩
    · exact ⟨1, by simpa using hb⟩
    · exact ⟨2, by simpa using hc⟩

theorem names_twice_mem {Γ} (p : Policy) (a : OrdinalExpression Γ) (x : PackedVariable Γ) :
    x ∈ names (AdmissiblePartial.twice p a) ↔ x ∈ names a := by
  unfold AdmissiblePartial.twice
  rw [names_expand_mem]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

theorem supported_three {Γ} {S : List (PackedVariable Γ)} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) (ha : Supported S a) (hb : Supported S b)
    (hc : Supported S c) : Supported S (AdmissiblePartial.three p site a b c) := by
  intro x hx
  rcases (names_three_mem p site a b c x).mp hx with h | h | h
  · exact ha x h
  · exact hb x h
  · exact hc x h

theorem supported_twice {Γ} {S : List (PackedVariable Γ)} (p : Policy)
    (a : OrdinalExpression Γ) (ha : Supported S a) : Supported S (AdmissiblePartial.twice p a) :=
  fun x hx => ha x ((names_twice_mem p a x).mp hx)

theorem supported_repeated {Γ} {S : List (PackedVariable Γ)} (p : Policy) (site : MacroSite)
    (count : Nat) (t : OrdinalExpression Γ) (ht : Supported S t) :
    Supported S (AdmissibleAssignment.repeated p site count t) := by
  cases count with
  | zero => simp [AdmissibleAssignment.repeated, Supported]
  | succ n => exact supported_expand (p.shape site n) (fun _ => t) (fun _ => ht)

theorem names_repeated_mem {Γ} (p : Policy) (site : MacroSite) (count : Nat)
    (t : OrdinalExpression Γ) (hc : 0 < count) (x : PackedVariable Γ) :
    x ∈ names (AdmissibleAssignment.repeated p site count t) ↔ x ∈ names t := by
  cases count with
  | zero => omega
  | succ n =>
    rw [AdmissibleAssignment.repeated, names_expand_mem]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

theorem supported_numeral {Γ} {S : List (PackedVariable Γ)} (p : Policy) (n : Nat) :
    Supported S (AdmissibleAssignment.numeral p n) :=
  supported_repeated p .numeral n .one (by simp [Supported])

end LogicLineages.OrdinalComparison.Source.AssignmentSupport.Proof

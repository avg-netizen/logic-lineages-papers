import LogicLineages.PersistentMarking.ProtectedSpineEncodingProof
import LogicLineages.PersistentMarking.MarkedBaseTupleRestrictionProof

namespace LogicLineages.PersistentMarking.ProtectedSpineLambdaCallProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineInterpreterCore ProtectedSpineLaws

def lambdaEvaluation (E : Environment) (σ ρ : Ty) (body : Evaluation) : Evaluation where
  value := lambdaValue E σ ρ body
  nonempty := lambdaCall E σ ρ body

inductive PrefixCase (σ ρ : Ty) : List Ty → Ty → Prop where
  | last : PrefixCase σ ρ [σ] ρ
  | more : (d::ds,τ) ∈ fullPrefixes ρ → PrefixCase σ ρ (σ::d::ds) τ

theorem prefixCase (σ ρ : Ty) (ds : List Ty) (τ : Ty)
    (hp : (ds,τ) ∈ fullPrefixes (.arrow σ ρ)) : PrefixCase σ ρ ds τ := by
  rcases List.mem_cons.mp hp with h | h
  · cases h
    exact .last
  · obtain ⟨⟨tail,v⟩,ha,he⟩ := List.mem_map.mp h
    cases he
    cases tail with
    | nil => exact False.elim ((FinitePrefixProof.forward ρ [] v ha).1 rfl)
    | cons d ds => exact .more ha

theorem last (E : Environment) (σ ρ : Ty) (body : Evaluation) (Γ : Context)
    (a : Assignments) (k : Nat) (x : Code) :
    nonemptyAt E (lambdaEvaluation E σ ρ body) Γ a k [σ] ρ [x] =
      codeAt E ρ body Γ (a.push σ x) := by
  simp [nonemptyAt,lambdaEvaluation,lambdaCall,Assignments.push,codeAt,valueAt]

theorem more (E : Environment) (σ ρ : Ty) (body : Evaluation) (Γ : Context)
    (a : Assignments) (k : Nat) (d : Ty) (ds : List Ty) (τ : Ty) (x y : Code) (xs : List Code) :
    nonemptyAt E (lambdaEvaluation E σ ρ body) Γ a k (σ::d::ds) τ (x::y::xs) =
      nonemptyAt E body Γ (a.push σ x) (k+1) (d::ds) τ (y::xs) := by
  simp [nonemptyAt,lambdaEvaluation,lambdaCall,Assignments.push]

theorem callValid (E : Environment) (σ ρ : Ty) (body : Evaluation) (hl : EvaluationLaws E ρ body)
    (Γ : Context) (a : Assignments) (k : Nat) (ds : List Ty) (τ : Ty) (xs : List Code)
    (ha : InputValid E Γ a) (hp : (ds,τ) ∈ fullPrefixes (.arrow σ ρ)) (hx : TupleValues E Γ ds xs) :
    nonemptyAt E (lambdaEvaluation E σ ρ body) Γ a k ds τ xs ∈ (descriptor E τ).carriers Γ := by
  cases prefixCase σ ρ ds τ hp with
  | last =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have ht := (HereditaryTupleProof.tupleCons E Γ σ [] x xs).mp hx
      cases xs with
      | nil =>
        rw [last]
        exact (ProtectedSpineEncodingProof.encodeAt E ρ body hl Γ (a.push σ x)
          (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1)).1
      | cons y ys => cases ht.2.1
  | @more d ds τ hp =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have ht := (HereditaryTupleProof.tupleCons E Γ σ (d::ds) x xs).mp hx
      cases xs with
      | nil => cases ht.2.1
      | cons y ys =>
        rw [more]
        exact hl.callValid Γ _ (k+1) _ _ _ (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1) hp ht.2

theorem callNatural (E : Environment) (σ ρ : Ty) (body : Evaluation) (hl : EvaluationLaws E ρ body)
    (Γ Δ : Context) (a : Assignments) (k : Nat) (ds : List Ty) (τ : Ty) (xs : List Code)
    (ha : InputValid E Γ a) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hp : (ds,τ) ∈ fullPrefixes (.arrow σ ρ)) (hx : TupleValues E Γ ds xs) :
    (descriptor E τ).restrict Γ Δ (nonemptyAt E (lambdaEvaluation E σ ρ body) Γ a k ds τ xs) =
      nonemptyAt E (lambdaEvaluation E σ ρ body) Δ (a.restrict E Γ Δ) k ds τ
        (restrictValues E Γ Δ ds xs) := by
  cases prefixCase σ ρ ds τ hp with
  | last =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have ht := (HereditaryTupleProof.tupleCons E Γ σ [] x xs).mp hx
      cases xs with
      | nil =>
        change _ = nonemptyAt E (lambdaEvaluation E σ ρ body) Δ (a.restrict E Γ Δ) k [σ] ρ
          [(descriptor E σ).restrict Γ Δ x]
        rw [last,last]
        exact ProtectedSpineEncodingProof.codeNatural E ρ body hl Γ Δ (a.push σ x)
          (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1) hd he
      | cons y ys => cases ht.2.1
  | @more d ds τ hp =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have ht := (HereditaryTupleProof.tupleCons E Γ σ (d::ds) x xs).mp hx
      cases xs with
      | nil => cases ht.2.1
      | cons y ys =>
        change _ = nonemptyAt E (lambdaEvaluation E σ ρ body) Δ (a.restrict E Γ Δ) k (σ::d::ds) τ
          ((descriptor E σ).restrict Γ Δ x :: (descriptor E d).restrict Γ Δ y :: restrictValues E Γ Δ ds ys)
        rw [more,more]
        exact hl.callNatural Γ Δ _ (k+1) _ _ _ (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1)
          hd he hp ht.2

theorem callOrder (E : Environment) (σ ρ : Ty) (body : Evaluation) (hl : EvaluationLaws E ρ body)
    (Γ : Context) (a b : Assignments) (k : Nat) (ds : List Ty) (τ : Ty) (xs ys : List Code)
    (ha : InputValid E Γ a) (hb : InputValid E Γ b) (hab : InputLE E Γ a b)
    (hp : (ds,τ) ∈ fullPrefixes (.arrow σ ρ)) (hx : TupleValues E Γ ds xs)
    (hy : TupleValues E Γ ds ys) (hxy : ValuesLE E Γ ds xs ys) :
    (descriptor E τ).le Γ (nonemptyAt E (lambdaEvaluation E σ ρ body) Γ a k ds τ xs)
      (nonemptyAt E (lambdaEvaluation E σ ρ body) Γ b k ds τ ys) = true := by
  cases prefixCase σ ρ ds τ hp with
  | last =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      cases ys with
      | nil => cases hy.1
      | cons y ys =>
        have ht := (HereditaryTupleProof.tupleCons E Γ σ [] x xs).mp hx
        have hu := (HereditaryTupleProof.tupleCons E Γ σ [] y ys).mp hy
        cases xs with
        | cons z zs => cases ht.2.1
        | nil =>
          cases ys with
          | cons z zs => cases hu.2.1
          | nil =>
            rw [last,last]
            exact ProtectedSpineEncodingProof.codeOrder E ρ body hl Γ _ _
              (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1)
              (ProtectedSpineInputProof.pushValid E Γ b σ y hb hu.1)
              (ProtectedSpineInputProof.pushOrder E Γ a b σ x y ha.1 hab (hxy 0 σ x y rfl rfl rfl))
  | @more d ds τ hp =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      cases ys with
      | nil => cases hy.1
      | cons y ys =>
        have ht := (HereditaryTupleProof.tupleCons E Γ σ (d::ds) x xs).mp hx
        have hu := (HereditaryTupleProof.tupleCons E Γ σ (d::ds) y ys).mp hy
        have hv := (MarkedBaseTupleFoundationProof.valuesCons E Γ σ (d::ds) x y xs ys).mp hxy
        cases xs with
        | nil => cases ht.2.1
        | cons v vs =>
          cases ys with
          | nil => cases hu.2.1
          | cons w ws =>
            rw [more,more]
            exact hl.callMonotone Γ _ _ (k+1) _ _ _ _
              (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1)
              (ProtectedSpineInputProof.pushValid E Γ b σ y hb hu.1)
              (ProtectedSpineInputProof.pushOrder E Γ a b σ x y ha.1 hab hv.1) hp ht.2 hu.2 hv.2

end LogicLineages.PersistentMarking.ProtectedSpineLambdaCallProof

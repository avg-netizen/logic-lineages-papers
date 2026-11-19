module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphIndexProof
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationASTProof
public import LogicLineages.ControlSensitivityCurrent.FullSortStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison.Source
open RawSourceDAG (variableIndex)
open CurrentUnitElimination (WireCtx shift)

/-- Typed lookup at a genuine ground position returns that exact position. -/
theorem indexSlot {Γ} (hg : ∀ σ ∈ Γ, σ = .ground) (fallback : Variable Γ .ground)
    {i : Nat} (hi : i<Γ.length) : variableIndex (slot fallback i)=i := by
  obtain ⟨σ,x,hx⟩ := atIndex i hi
  obtain rfl : σ = .ground := hg σ (varMem x)
  have he := RawSourceDAG.variable_roundtrip x
  rw [hx] at he
  simp only [slot,he,Option.getD_some,hx]

theorem slotAt {Γ} (fallback x : Variable Γ .ground) : slot fallback (variableIndex x)=x := by
  simp only [slot,RawSourceDAG.variable_roundtrip,Option.getD_some]

theorem indexRoute {Γ Ξ} (hg : ∀ σ ∈ Γ, σ = .ground) (hΞ : ∀ σ ∈ Ξ, σ = .ground)
    (fallback : Variable Ξ .ground) (idx : Nat→Nat) {σ} (x : Variable Γ σ)
    (hi : idx (variableIndex x)<Ξ.length) : variableIndex (route hg fallback idx x)=idx (variableIndex x) := by
  obtain rfl : σ = .ground := hg σ (varMem x)
  change variableIndex (slot fallback (idx (variableIndex x))) = idx (variableIndex x)
  exact indexSlot hΞ fallback hi

theorem groundRoute {Γ Ξ} (hg : ∀ σ ∈ Γ, σ = .ground) (z : Variable Ξ .ground)
    (idx : Nat→Nat) (x : Variable Γ .ground) :
    route hg z idx x = slot z (idx (variableIndex x)) := rfl

theorem groundCons {Γ} (hg : ∀ σ ∈ Γ, σ = .ground) : ∀ σ ∈ .ground :: Γ, σ = .ground := by
  intro σ h
  rcases List.mem_cons.mp h with rfl|h
  · rfl
  · exact hg σ h

theorem directGround : ∀ σ ∈ DirectCtx, σ = .ground := groundCons (groundCons (by simp))

theorem exactS : Targets.ExactS := by
  intro p f hf n
  let ν : Variable [.ground] .ground → Nat := ExistentialPlan.extend (fun x => nomatch x) n
  let x : Variable [.ground] .ground := .here
  let ρ := ExistentialPlan.inputs ν
  have hS : actualS.term = (.succC : OriginalTerm [] (.arrow .ground .ground)) :=
    (CurrentTreeInputCoverage.StatementChecks.actual_tree_codes [] (.arrow .ground .ground) .succC).1
  have hcall : (BooleanCompiler.call actualS x).term = successorProbe x := by
    rw [SourceAST.call_term,hS]
    rfl
  have H := (FullSort.StatementChecks.fixed_completeSort f hf).2.2 p
  have ht : SourceSortCompletion.input ρ x = n := rfl
  obtain ⟨v,hv,he⟩ := ((H.1 [.ground] ρ x (f (n+4))).2 (by rw [ht]))
  unfold SourceAST.callValue InputNormalization.sourceValue
  change PolicyCollision.rawScalar p f ρ (BooleanCompiler.call actualS x).term-1=f (n+4)
  unfold PolicyCollision.rawScalar
  rw [hcall,hv]
  simp only [Option.map_some,Option.getD_some,he,OriginalDomain.finiteValue,Ordinal.card_nat,Cardinal.toNat_natCast]
  omega

/-- Any literal algebra map on the emitted grammar. Bounds apply only to
variable lookup, never to numeric values or the sizes of literal constants. -/
structure LayoutMap {A F B G : Type} (l : Layout A F) (r : Layout B G)
    (ta : A→B) (fa : F→G) (limit : Nat) : Prop where
  varAt : ∀ i, i<limit → ta (l.var i)=r.var i
  constant : ∀ n, ta (l.lit n)=r.lit n
  addition : ∀ a b, ta (l.add a b)=r.add (ta a) (ta b)
  successor : ∀ a, ta (l.succCall a)=r.succCall (ta a)
  equality : ∀ a b, fa (l.eq a b)=r.eq (ta a) (ta b)
  ordering : ∀ a b, fa (l.le a b)=r.le (ta a) (ta b)
  conjoin : ∀ a b, fa (l.and a b)=r.and (fa a) (fa b)
  disjoin : ∀ a b, fa (l.or a b)=r.or (fa a) (fa b)
  trueValue : fa l.yes=r.yes
  falseValue : fa l.no=r.no

namespace LayoutMap
variable {A F B G : Type} {l : Layout A F} {r : Layout B G} {ta : A→B} {fa : F→G} {limit : Nat}

theorem foldAnd (h : LayoutMap l r ta fa limit) (xs : List F) :
    fa (xs.foldr l.and l.yes)=(xs.map fa).foldr r.and r.yes := by
  induction xs <;> simp only [List.foldr_nil,List.map_nil,List.foldr_cons,List.map_cons,h.trueValue,h.conjoin,*]
theorem foldOr (h : LayoutMap l r ta fa limit) (xs : List F) (a : F) :
    fa (xs.foldr l.or a)=(xs.map fa).foldr r.or (fa a) := by
  induction xs <;> simp only [List.foldr_nil,List.map_nil,List.foldr_cons,List.map_cons,h.disjoin,*]

theorem gate (h : LayoutMap l r ta fa limit) (small : List Nat) (u v arg : Nat)
    (hu : u<limit) (hv : v<limit) (ha : arg<limit) :
    fa (fGate l small u v arg)=fGate r small u v arg := by
  unfold fGate
  rw [h.foldOr]
  simp [List.map_map,Function.comp_def,h.conjoin,h.equality,h.varAt _ hu,h.varAt _ hv,h.varAt _ ha,
    h.constant,h.addition,h.successor]

theorem finitePart (h : LayoutMap l r ta fa limit) (t y : Nat) (ht : t<limit) (hy : y<limit)
    (n : Nat) (vs : List Nat) : fa (prefixBody l t y n vs)=prefixBody r t y n vs := by
  induction vs generalizing n with
  | nil => exact h.falseValue
  | cons v vs ih =>
    simp only [prefixBody,h.disjoin,h.conjoin,h.equality,h.varAt _ ht,h.varAt _ hy,h.constant,ih]

theorem tailPart (h : LayoutMap l r ta fa limit) (w δ nξ base : Nat)
    (hlim : directWidth w δ+1<limit) (small : List Nat) (a : F) :
    fa (tailBody l w δ nξ base small a)=tailBody r w δ nξ base small (fa a) := by
  unfold tailBody
  rw [h.foldAnd,List.map_append]
  have ht : directWidth w δ<limit := by omega
  have hz : w+1<limit := by unfold directWidth at hlim; omega
  have hzero : w+2<limit := by unfold directWidth at hlim; omega
  have hv : w<limit := by omega
  have hu : uSlot w 0<limit := by unfold uSlot directWidth at *; omega
  have hud : uSlot w δ<limit := by unfold uSlot directWidth at *; omega
  simp only [List.map_cons,List.map_nil,h.ordering,h.equality,h.addition,h.constant,h.varAt _ ht,
    h.varAt _ hlim,h.varAt _ hz,h.varAt _ hzero,h.varAt _ hv,h.varAt _ hu,h.varAt _ hud]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hh := List.mem_range.mp hj
  apply h.gate
  · unfold uSlot directWidth at *; omega
  · unfold uSlot directWidth at *; omega
  · unfold argSlot directWidth at *; omega

theorem wholePart (h : LayoutMap l r ta fa limit) (w δ nξ base : Nat)
    (hlim : directWidth w δ+1<limit) (small points : List Nat) (a : F) :
    fa (directBody l w δ nξ base small points a)=directBody r w δ nξ base small points (fa a) := by
  unfold directBody
  rw [h.disjoin,h.finitePart _ _ (by omega) hlim,h.tailPart _ _ _ _ hlim]

theorem splicePart (h : LayoutMap l r ta fa limit) (b c g nξ level : Nat)
    (hi : operandEnd b c g+2<limit) (l₁ l₂ l₃ : F) :
    fa (insertedBody l b c g nξ level l₁ l₂ l₃)=insertedBody r b c g nξ level (fa l₁) (fa l₂) (fa l₃) := by
  unfold insertedBody
  have he : operandEnd b c g<limit := by omega
  have he' : operandEnd b c g+1<limit := by omega
  simp only [h.conjoin,h.equality,h.addition,h.varAt _ hi,h.varAt _ he,h.varAt _ he',h.constant]
end LayoutMap

theorem codeLayout {Γ} (hg : ∀ σ ∈ Γ, σ = .ground) (z : Variable Γ .ground) :
    LayoutMap (typedLayout z) rawLayout MatrixCode.term MatrixCode.formula Γ.length := by
  constructor
  · intro i hi
    change MatrixCode.var (variableIndex (slot z i)) = MatrixCode.var i
    rw [indexSlot hg z hi]
  all_goals intros; rfl

def evalLayout (f : Nat→Nat) (w : Nat→Nat) : Layout Nat Bool where
  var := w
  lit := id
  add := Nat.add
  succCall := fun n => f (n+4)
  eq := fun a b => decide (a=b)
  le := fun a b => decide (a≤b)
  and := (· && ·)
  or := (· || ·)
  yes := true
  no := false

theorem evalMap (p : LogicLineages.OrdinalComparison.Source.AdmissibleSum.Policy) (f : Nat→Nat)
    (hf : FullAddition.Targets.SourceGrowth f) {Γ} (z : Variable Γ .ground) (ν : Variable Γ .ground→Nat)
    (n : Nat) (w : Nat → Nat) (hw : ∀ i, i < n → ν (slot z i)=w i) :
    LayoutMap (typedLayout z) (evalLayout f w)
      (SourceAST.Term.eval p f ν) (SourceAST.Formula.eval p f ν) n := by
  constructor
  · exact hw
  · intros; rfl
  · intros; rfl
  · intro a
    exact exactS p f hf _
  all_goals intros; rfl

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

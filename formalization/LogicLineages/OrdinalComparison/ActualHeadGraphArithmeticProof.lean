module
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticTargets
public import LogicLineages.OrdinalComparison.SourceSortCompletionStatementChecks
public import LogicLineages.OrdinalComparison.WWSelectedBinderStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic.Proof

 theorem rename_value (e : Expr) (r : Nat → Nat) (ν : Nat → Nat) :
    (e.rename r).value ν=e.value (fun i => ν (r i)) := by
  induction e with
  | numeral n | «variable» i => rfl
  | add a b ia ib => simp only [Expr.rename,Expr.value,ia,ib]
  | scale n a ia => simp only [Expr.rename,Expr.value,ia]

 theorem lift_one (e : Expr) (ν : Nat → Nat) (n : Nat) :
    (e.lift 1).value (extend ν n)=e.value ν := by
  rw [Expr.lift,rename_value]
  rfl

 theorem lift_two (e : Expr) (ν : Nat → Nat) (n m : Nat) :
    (e.lift 2).value (extend (extend ν n) m)=e.value ν := by
  rw [Expr.lift,rename_value]
  rfl

 theorem lift_three (e : Expr) (ν : Nat → Nat) (n m k : Nat) :
    (e.lift 3).value (extend (extend (extend ν n) m) k)=e.value ν := by
  rw [Expr.lift,rename_value]
  rfl

 theorem conjunction_eval (xs : List Formula) (ν : Nat → Nat) :
    (conjunction xs).eval ν ↔ ∀ p∈xs,p.eval ν := by
  induction xs with
  | nil => simp [conjunction,Formula.eval]
  | cons p ps ih => simpa [conjunction,Formula.eval] using
      (and_congr Iff.rfl ih)

 theorem disjunction_eval (xs : List Formula) (ν : Nat → Nat) :
    (disjunction xs).eval ν ↔ ∃ p∈xs,p.eval ν := by
  induction xs with
  | nil => simp [disjunction,Formula.eval]
  | cons p ps ih => simpa [disjunction,Formula.eval] using
      (or_congr Iff.rfl ih)

 theorem successor_eval (a b : Expr) (ν : Nat → Nat) :
    (successor a b).eval ν ↔ b.value ν=Phi (a.value ν+4) := by
  let ρ : OrdinalComponent [Ty.ground] → Nat :=
    fun c => ([a].getD (SourceTypedPorts.variableIndex c.2.1) (.numeral 0)).value ν
  change SourceSortCompletion.Observation ρ (successorProbe .here) (b.value ν) ↔ _
  simpa only [SourceSortCompletion.input,ρ,SourceTypedPorts.variableIndex,List.getD_cons_zero]
    using SourceSortCompletion.StatementChecks.fullSourceSort.1 [Ty.ground] ρ .here (b.value ν)

 theorem small_phi (a b : Expr) (ν : Nat → Nat) :
    (disjunction ((List.range 4).map fun i =>
      Formula.and (.eq a (.numeral i)) (.eq b (.numeral (Phi i))))).eval ν ↔
      a.value ν<4 ∧ b.value ν=Phi (a.value ν) := by
  rw [disjunction_eval]
  simp only [List.mem_map,Formula.eval,Expr.value]
  constructor
  · rintro ⟨p,⟨i,hi,rfl⟩,ha,hb⟩
    change a.value ν=i at ha
    change b.value ν=Phi i at hb
    exact ⟨ha ▸ List.mem_range.mp hi,by simpa only [ha] using hb⟩
  · rintro ⟨ha,hb⟩
    exact ⟨_,⟨a.value ν,List.mem_range.mpr ha,rfl⟩,rfl,hb⟩

 theorem fullPhiGate : Targets.FullPhiGate := by
  intro a b ν
  change (_ ∨ ∃ n : Nat, _) ↔ _
  rw [small_phi]
  simp only [Formula.eval,lift_one,Expr.value,extend,successor_eval]
  constructor
  · rintro (⟨_,hb⟩ | ⟨n,ha,hb⟩)
    · exact hb
    · simpa only [ha] using hb
  · intro hb
    by_cases ha : a.value ν<4
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨a.value ν-4,by omega,by simpa only [Nat.sub_add_cancel (by omega : 4≤a.value ν)] using hb⟩

 theorem fixedPhiChain : Targets.FixedPhiChain := by
  intro d
  induction d with
  | zero => intro a b ν; rfl
  | succ d ih =>
      intro a b ν
      change (∃ n : Nat, (phi (a.lift 1) (.variable 0)).eval (extend ν n) ∧
        (phiChain d (.variable 0) (b.lift 1)).eval (extend ν n)) ↔ _
      have hp : ∀ (a b : Expr) (ν : Nat → Nat),
          (phi a b).eval ν ↔ b.value ν=Phi (a.value ν) := fullPhiGate
      simp only [hp,ih,lift_one,Expr.value,extend]
      simp only [exists_eq_left,Function.iterate_succ_apply]


 theorem map_lift_getD (xs : List Expr) (i k : Nat) :
    (xs.map (Expr.lift k)).getD i (.numeral 0)=(xs.getD i (.numeral 0)).lift k := by
  induction xs generalizing i with
  | nil => simp [Expr.lift,Expr.rename]
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.map_cons,List.getD_cons_succ] using ih i

 theorem input_lift_one {Γ} (xs : List Expr) (ν : Nat → Nat) (n : Nat) :
    inputValues (Γ:=Γ) (extend ν n) (xs.map (Expr.lift 1))=inputValues ν xs := by
  funext x
  simp only [inputValues,map_lift_getD,lift_one]

 theorem input_lift_two {Γ} (xs : List Expr) (ν : Nat → Nat) (n m : Nat) :
    inputValues (Γ:=Γ) (extend (extend ν n) m) (xs.map (Expr.lift 2))=inputValues ν xs := by
  funext x
  simp only [inputValues,map_lift_getD,lift_two]

 theorem input_lift_three {Γ} (xs : List Expr) (ν : Nat → Nat) (n m k : Nat) :
    inputValues (Γ:=Γ) (extend (extend (extend ν n) m) k) (xs.map (Expr.lift 3))=inputValues ν xs := by
  funext x
  simp only [inputValues,map_lift_getD,lift_three]

 theorem leaf_inputs {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (xs : List Expr) (ν : Nat → Nat) (x y q : Nat) :
    (fun c : OrdinalComponent (.ground::.ground::Γ) =>
      ((Expr.variable 2 :: Expr.variable 1 :: xs.map (Expr.lift 3)).getD
        (SourceTypedPorts.variableIndex c.2.1) (.numeral 0)).value
          (extend (extend (extend ν x) y) q)) =
    AbsoluteObserver.extend (UnitElimination.inputs (inputValues ν xs)) x y := by
  funext c
  rcases c with ⟨σ,v,j⟩
  cases v with
  | here => rfl
  | there v =>
      cases v with
      | here => rfl
      | there v =>
          have hs := AbsoluteObserver.groundType hΓ v
          subst σ
          change ((xs.map (Expr.lift 3)).getD (SourceTypedPorts.variableIndex v) (.numeral 0)).value
            (extend (extend (extend ν x) y) q) =
            (xs.getD (SourceTypedPorts.variableIndex v) (.numeral 0)).value ν
          simp only [map_lift_getD,lift_three]

 theorem removed_length (left right : List Ty) (σ : Ty) (xs : List Expr)
    (hlen : (left++σ::right).length≤xs.length) :
    (left++right).length≤(xs.take left.length ++ xs.drop (left.length+1)).length := by
  simp only [List.length_append,List.length_cons] at hlen
  simp only [List.length_append,List.length_take,List.length_drop]
  rw [Nat.min_eq_left (by omega : left.length≤xs.length)]
  omega

 theorem removed_inputs (left right : List Ty) (σ : Ty) (xs : List Expr)
    (hlen : (left++σ::right).length≤xs.length) (ν : Nat → Nat) :
    inputValues (Γ:=left++right) ν (xs.take left.length ++ xs.drop (left.length+1))=
      UnitObservation.remainingInputs left right σ (inputValues ν xs) := by
  induction left generalizing xs with
  | nil =>
      cases xs with
      | nil => simp at hlen
      | cons a xs => rfl
  | cons τ left ih =>
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
          have hlen' : (left++σ::right).length≤xs.length := by simpa using hlen
          funext v
          cases v with
          | here => rfl
          | there v =>
              simpa only [List.length_cons,List.take_succ_cons,List.drop_succ_cons,List.cons_append,
                inputValues,SourceTypedPorts.variableIndex,List.getD_cons_succ,
                UnitObservation.remainingInputs,SelectedBinder.moveFromHead,
                SelectedBinder.swap,Renaming.lift] using congrFun (ih xs hlen') v

 theorem unitTreeExpansion : Targets.UnitTreeExpansion := by
  intro Γ q
  induction q with
  | leaf b =>
      intro xs hlen r ν
      simp only [unitFormula,Formula.eval,conjunction,List.foldr_cons,List.foldr_nil,
        Expr.value,extend,lift_three,leaf_inputs b.allGround,UnitElimination.Eval,
        and_true]
  | free left right σ d q ih =>
      intro xs hlen r ν
      have hlen' := removed_length left right σ xs hlen
      simp only [unitFormula,Formula.eval,UnitElimination.Eval]
      apply exists_congr
      intro l
      rw [ih _ (by simpa only [List.length_map] using hlen')]
      simp only [input_lift_one,removed_inputs left right σ xs hlen,lift_one,Expr.value,extend]
  | active left right σ p d d' c q s ihq ihs =>
      intro xs hlen r ν
      have hlen' := removed_length left right σ xs hlen
      simp only [unitFormula,Formula.eval,UnitElimination.Eval]
      apply exists_congr
      intro l
      apply exists_congr
      intro l'
      simp only [conjunction,List.foldr_cons,List.foldr_nil,Formula.eval,and_true]
      rw [ihq _ (by simpa only [List.length_map] using hlen'),
        ihs _ (by simpa only [List.length_map] using hlen')]
      simp only [input_lift_two,removed_inputs left right σ xs hlen,lift_two,Expr.value,extend]

end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic.Proof

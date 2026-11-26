module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationFreeProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open CurrentOneUnit ExistentialPlan

private abbrev Ambient (Γ : List Ty) (m n : Nat) :=
  Ty.ground :: Ty.ground :: WireCtx m (WireCtx n (.ground :: Γ))

private def ambientEq (Γ : List Ty) (m n : Nat) :
    Ambient Γ m n = WireCtx ((m+n)+2) (.ground :: Γ) :=
  congrArg (fun C => .ground :: .ground :: C) (wireCtx_add m n (.ground :: Γ)).symm

private def ambientCast (Γ : List Ty) (m n : Nat) :
    Renaming (Ambient Γ m n) (WireCtx ((m+n)+2) (.ground :: Γ)) :=
  fun {τ} x => cast (congrArg (fun C => Variable C τ) (ambientEq Γ m n)) x

private def leftBase (Γ : List Ty) (m n : Nat) :
    Renaming (WireCtx m Γ) (Ambient Γ m n) :=
  fun x => .there (.there (under (fun y => shift n (.there y)) m x))

private def rightBase (Γ : List Ty) (m n : Nat) :
    Renaming (WireCtx n Γ) (Ambient Γ m n) :=
  fun x => .there (.there (shift m (under (Renaming.weaken Γ .ground) n x)))

private def outputPort (Γ : List Ty) (m n : Nat) : Variable (Ambient Γ m n) .ground :=
  .there (.there (shift m (shift n .here)))

private theorem activeMatrix (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (row : LinearCode) (q s : OpenGraph Γ)
    (η : Variable (WireCtx ((q.width+s.width)+2) (.ground :: Γ)) .ground → Nat) :
    (activeGraph row q s).matrix.eval p f η = true ↔
      let ω : Variable (Ambient Γ q.width s.width) .ground → Nat :=
        fun x => η (ambientCast Γ q.width s.width x)
      (q.matrix.eval p f (fun x => ω (reroute q.width (leftBase Γ q.width s.width) .here x)) = true ∧
      s.matrix.eval p f (fun x => ω (reroute s.width (rightBase Γ q.width s.width) (.there .here) x)) = true) ∧
      holds row (ω .here+1) (ω (.there .here)+1) (ω (outputPort Γ q.width s.width)+1) := by
  change ((renameFormula (ambientCast Γ q.width s.width)
    (.conj (.conj (renameFormula (reroute q.width (leftBase Γ q.width s.width) .here) q.matrix)
        (renameFormula (reroute s.width (rightBase Γ q.width s.width) (.there .here)) s.matrix))
      (rowFormula row (raw .here) (raw (.there .here)) (raw (outputPort Γ q.width s.width))))).eval p f η = true) ↔ _
  simp only [formulaEvalRename,SourceAST.Formula.eval,Bool.and_eq_true,evalRow,evalRaw]

private theorem sharedPort (Γ : List Ty) (m n : Nat) (x : Variable (.ground :: Γ) .ground) :
    ambientCast Γ m n (.there (.there (shift m (shift n x)))) =
      shift ((m+n)+2) x :=
  shiftCastTwo m n x

theorem exactActiveNat (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : Variable Γ .ground → Nat) (row : LinearCode) (q s : OpenGraph Γ) (n : Nat) :
    (activeGraph row q s).holds p f ρ n ↔
      ∃ l l' : Nat, q.holds p f ρ l ∧ s.holds p f ρ l' ∧ holds row (l+1) (l'+1) (n+1) := by
  let m := q.width
  let k := s.width
  constructor
  · rintro ⟨η,hρ,hn,hM⟩
    let ω : Variable (Ambient Γ m k) .ground → Nat := fun x => η (ambientCast Γ m k x)
    obtain ⟨⟨hQ,hS⟩,hrow⟩ := (activeMatrix p f row q s η).1 hM
    have hshift (x : Variable (.ground :: Γ) .ground) :
        ω (.there (.there (shift m (shift k x)))) = η (shift ((m+k)+2) x) :=
      congrArg η (sharedPort Γ m k x)
    refine ⟨ω .here,ω (.there .here),
      routeHolds p f q (leftBase Γ m k) .here ω ρ ?_ hQ,
      routeHolds p f s (rightBase Γ m k) (.there .here) ω ρ ?_ hS,?_⟩
    · intro x
      change ω (.there (.there (under (fun z => shift k (.there z)) m (shift m x)))) = ρ x
      rw [pullShiftUnder,hshift]
      exact hρ x
    · intro x
      change ω (.there (.there (shift m (under (Renaming.weaken Γ .ground) k (shift k x))))) = ρ x
      rw [pullShiftUnder,hshift]
      exact hρ x
    · have hroot : ω (outputPort Γ m k) = n :=
        (hshift .here).trans hn
      change holds row (ω .here+1) (ω (.there .here)+1) (ω (outputPort Γ m k)+1) at hrow
      rwa [hroot] at hrow
  · rintro ⟨l,l',hQ,hS,hrow⟩
    obtain ⟨u,hu⟩ := (holdsFilled p f q ρ l).1 hQ
    obtain ⟨v,hv⟩ := (holdsFilled p f s ρ l').1 hS
    let ω : Variable (Ambient Γ m k) .ground → Nat :=
      extend (extend (fillPrefix m u (fillPrefix k v (extend ρ n))) l') l
    let η : Variable (WireCtx ((m+k)+2) (.ground :: Γ)) .ground → Nat :=
      fun x => ω (castGround (ambientEq Γ m k).symm x)
    have hη : (fun x => η (ambientCast Γ m k x)) = ω := by
      funext x
      exact congrArg ω (castGround_left_inverse (ambientEq Γ m k) x)
    have hshift (x : Variable (.ground :: Γ) .ground) :
        η (shift ((m+k)+2) x) = extend ρ n x := by
      rw [← sharedPort Γ m k x]
      calc
        _ = ω (.there (.there (shift m (shift k x)))) := congrFun hη _
        _ = _ := by
          change fillPrefix m u (fillPrefix k v (extend ρ n)) (shift m (shift k x)) = _
          rw [fillShift,fillShift]
    have hLeft : (fun x => ω (leftBase Γ m k x)) = fillPrefix m u ρ := by
      funext x
      change fillPrefix m u (fillPrefix k v (extend ρ n))
        (under (fun z => shift k (.there z)) m x) = _
      simp only [fillUnder,fillShift,extend]
    have hRight : (fun x => ω (rightBase Γ m k x)) = fillPrefix k v ρ := by
      funext x
      change fillPrefix m u (fillPrefix k v (extend ρ n))
        (shift m (under (Renaming.weaken Γ .ground) k x)) = _
      simp only [fillShift,fillUnder,Renaming.weaken,extend]
    have hQL := routeFill m (leftBase Γ m k) .here ω ρ u l hLeft rfl
    have hSR := routeFill k (rightBase Γ m k) (.there .here) ω ρ v l' hRight rfl
    refine ⟨η,fun x => hshift (.there x),hshift .here,(activeMatrix p f row q s η).2 ?_⟩
    dsimp only
    have hpoint (x : Variable (Ambient Γ q.width s.width) .ground) :
        η (ambientCast Γ q.width s.width x) = ω x := congrFun hη x
    simp only [hpoint]
    change (q.matrix.eval p f (fun x => ω (reroute m (leftBase Γ m k) .here x)) = true ∧
      s.matrix.eval p f (fun x => ω (reroute k (rightBase Γ m k) (.there .here) x)) = true) ∧
      holds row (ω .here+1) (ω (.there .here)+1) (ω (outputPort Γ m k)+1)
    refine ⟨⟨?_,?_⟩,?_⟩
    · rwa [hQL]
    · rwa [hSR]
    · have hroot : ω (outputPort Γ m k) = n := by
        change fillPrefix m u (fillPrefix k v (extend ρ n)) (shift m (shift k .here)) = n
        rw [fillShift,fillShift] <;> rfl
      rw [hroot]
      exact hrow

theorem activeConjunctive {Γ : List Ty} (row : LinearCode) (q s : OpenGraph Γ)
    (h : Conjunctive q.matrix) (h' : Conjunctive s.matrix) :
    Conjunctive (activeGraph row q s).matrix := by
  apply formulaRetainsGrammar
  exact ⟨⟨formulaRetainsGrammar _ _ h,formulaRetainsGrammar _ _ h'⟩,
    rowConjunctive row _ _ _ (rawLinear _) (rawLinear _) (rawLinear _)⟩

theorem exactComposition : CurrentUnitEliminationTargets.ExactComposition := by
  intro p f Γ ρ row n q s
  constructor
  · rw [rawSucc,exactFreeNat]
    constructor
    · rintro ⟨l,hl,hrow⟩
      exact ⟨l+1,⟨l,rfl,hl⟩,hrow⟩
    · rintro ⟨_,⟨l,rfl,hl⟩,hrow⟩
      exact ⟨l,hl,hrow⟩
  · rw [rawSucc,exactActiveNat]
    constructor
    · rintro ⟨l,l',hl,hl',hrow⟩
      exact ⟨l+1,l'+1,⟨l,rfl,hl⟩,⟨l',rfl,hl'⟩,hrow⟩
    · rintro ⟨_,_,⟨l,rfl,hl⟩,⟨l',rfl,hl'⟩,hrow⟩
      exact ⟨l,l',hl,hl',hrow⟩

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

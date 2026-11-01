module
public import LogicLineages.OrdinalComparison.OneNameSourceBooleanTargets
public import LogicLineages.OrdinalComparison.GroundSourceEqualityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneNameSourceBoolean
open Source Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def scalarPositive {ι : Type} : Scalar ι → FixedLimitPositiveExpr
  | .one => .constant 1
  | .var _ => .input
  | .add E F => .add (scalarPositive E) (scalarPositive F)
  | .shift c E => .head (scalarHeadNote c) (scalarPositive E)

theorem scalar_valid {ι : Type} (E : Scalar ι) : fixedLimitProfileBelow epsilonZero (scalarPositive E) := by
  induction E with
  | one => trivial
  | var i => trivial
  | add E F ihE ihF => exact ⟨ihE,ihF⟩
  | shift c E ih => exact ⟨(MultivariateSourceBridge.head_limit c).1,(MultivariateSourceBridge.head_limit c).2.1,ih⟩

theorem scalar_value {ι : Type} (E : Scalar ι) (x : Nat) :
    actualFixedLimitProfileEval (scalarPositive E) x=E.value (fun _ => x) := by
  induction E with
  | one => rfl
  | var i => rfl
  | add E F ihE ihF => exact congrArg₂ (·+·) ihE ihF
  | shift c E ih =>
    simp only [scalarPositive,actualFixedLimitProfileEval,actualProfileHead,Scalar.value,
      MultivariateSourceBridge.scalar_head_value,ih]

theorem singleton_index {σ : Ty} (v : Variable [Ty.ground] σ) : SourceTypedPorts.variableIndex v=0 := by
  cases v with
  | here => rfl
  | there v => cases v

theorem scalar_code (E : Scalar (OrdinalComponent [Ty.ground])) :
    positiveExprEncode (scalarPositive E)=scalarCode (fun c => SourceTypedPorts.variableIndex c.2.1) E := by
  induction E with
  | one => rfl
  | var c =>
    change 1=4*SourceTypedPorts.variableIndex c.2.1+1
    rw [singleton_index]
  | add E F ihE ihF => simp only [scalarPositive,positiveExprEncode,scalarCode,ihE,ihF]
  | shift c E ih => simp only [scalarPositive,positiveExprEncode,scalarCode,ih]

theorem scalar_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v=some c)
    (ρ : OrdinalComponent Γ → Nat) :
    sourceVectorAtValue v ρ 0=(c.scalar.value ρ : Ordinal) := by
  have h := compiledVectorSound Γ n v c hc ρ 0
  simpa [sourceVectorAtValue,ordinalVectorAt,CompiledVector.value] using h.symm

theorem positive_field {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v=some c)
    (ρ : OrdinalComponent Γ → Nat) (j : Nat) :
    positiveNoteAt c.positiveNotes j=sourceVectorAtValue v ρ (j+1) := by
  by_cases hj : j<n
  · have h := compiledVectorSound Γ n v c hc ρ (Fin.succ ⟨j,hj⟩)
    simpa [positiveNoteAt,CompiledVector.positiveNotes,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,hj,sourceVectorAtValue,ordinalVectorAt,Nat.succ_lt_succ hj,
      CompiledVector.value] using h
  · have hp : c.positiveNotes.length≤j := by simpa [CompiledVector.positiveNotes] using Nat.le_of_not_gt hj
    rw [positiveNoteAt,List.getD_eq_default _ _ hp]
    simp [sourceVectorAtValue,ordinalVectorAt,show ¬j+1<n+1 by omega,zeroNote,denote]

def compiledAtomFormula {n m : Nat} (relation : OneInputOrderRelation)
    (ac : CompiledVector (OrdinalComponent [Ty.ground]) n) (bc : CompiledVector (OrdinalComponent [Ty.ground]) m) :
    OneInputBooleanExpr :=
  .conj (.truth (encodedOneNameSourceGuard (oneInputOrderRelationCode relation)
    (compiledQueryCode (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc)))
    (.atom relation (scalarPositive ac.scalar) (scalarPositive bc.scalar))

theorem compiled_valid {n m : Nat} (relation : OneInputOrderRelation)
    (ac : CompiledVector (OrdinalComponent [Ty.ground]) n) (bc : CompiledVector (OrdinalComponent [Ty.ground]) m) :
    oneInputBooleanValid (compiledAtomFormula relation ac bc) :=
  ⟨True.intro,scalar_valid ac.scalar,scalar_valid bc.scalar⟩

theorem compiled_point {n m : Nat} (relation : OneInputOrderRelation)
    (av : OrdinalVector [Ty.ground] n) (bv : OrdinalVector [Ty.ground] m)
    (ac : CompiledVector (OrdinalComponent [Ty.ground]) n) (bc : CompiledVector (OrdinalComponent [Ty.ground]) m)
    (ha : compileVector av=some ac) (hb : compileVector bv=some bc) (x : Nat) :
    actualOneInputBooleanValue (compiledAtomFormula relation ac bc) x=true ↔
      match relation with
      | .equal => GroundSourceEquality.SourceEqualityAt av bv (fun _ => x)
      | .weak => SourceComparisonAt false av bv (fun _ => x)
      | .strict => SourceComparisonAt true av bv (fun _ => x) := by
  cases relation with
  | equal =>
    change ((positiveComparison (normalCodes ac.positiveNotes) (normalCodes bc.positiveNotes) &&
      positiveComparison (normalCodes bc.positiveNotes) (normalCodes ac.positiveNotes)) &&
      decide (actualFixedLimitProfileEval (scalarPositive ac.scalar) x=
        actualFixedLimitProfileEval (scalarPositive bc.scalar) x))=true ↔ _
    rw [Bool.and_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq,
      positiveComparisonSourceCorrect,positiveComparisonSourceCorrect,scalar_value,scalar_value]
    constructor
    · rintro ⟨⟨hpos,hrev⟩,hz⟩ j
      cases j with
      | zero =>
        rw [scalar_field av ac ha _,scalar_field bv bc hb _]
        exact congrArg (fun n : Nat => (n : Ordinal)) hz
      | succ j =>
        rw [←positive_field av ac ha _ j,←positive_field bv bc hb _ j]
        exact le_antisymm (hpos j) (hrev j)
    · intro h
      have hp (j : Nat) : positiveNoteAt ac.positiveNotes j=positiveNoteAt bc.positiveNotes j := by
        rw [positive_field av ac ha _ j,positive_field bv bc hb _ j]
        exact h (j+1)
      refine ⟨⟨fun j => (hp j).le,fun j => (hp j).ge⟩,?_⟩
      have hz := h 0
      rw [scalar_field av ac ha _,scalar_field bv bc hb _] at hz
      exact_mod_cast hz
  | weak =>
    change (positiveComparison (normalCodes ac.positiveNotes) (normalCodes bc.positiveNotes) &&
      decide (actualFixedLimitProfileEval (scalarPositive ac.scalar) x≤
        actualFixedLimitProfileEval (scalarPositive bc.scalar) x))=true ↔ _
    rw [Bool.and_eq_true_iff,decide_eq_true_eq,positiveComparisonSourceCorrect,scalar_value,scalar_value]
    unfold SourceComparisonAt
    rw [scalar_field av ac ha _,scalar_field bv bc hb _]
    simp only [Bool.false_eq_true,if_false,Nat.cast_le,←positive_field av ac ha _,←positive_field bv bc hb _]
  | strict =>
    change (positiveComparison (normalCodes ac.positiveNotes) (normalCodes bc.positiveNotes) &&
      decide (actualFixedLimitProfileEval (scalarPositive ac.scalar) x<
        actualFixedLimitProfileEval (scalarPositive bc.scalar) x))=true ↔ _
    rw [Bool.and_eq_true_iff,decide_eq_true_eq,positiveComparisonSourceCorrect,scalar_value,scalar_value]
    unfold SourceComparisonAt
    rw [scalar_field av ac ha _,scalar_field bv bc hb _]
    simp only [if_true,Nat.cast_lt,←positive_field av ac ha _,←positive_field bv bc hb _]

end LogicLineages.OrdinalComparison.OneNameSourceBoolean

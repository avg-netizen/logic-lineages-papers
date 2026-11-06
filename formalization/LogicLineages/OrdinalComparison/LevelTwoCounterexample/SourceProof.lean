module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceTargets
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarProof
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarCodeProof
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairProof
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairCodeProof
import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof
import LogicLineages.OrdinalComparison.WWGroundTupleProof
import LogicLineages.OrdinalComparison.WWSourceClassesFullProof
import LogicLineages.OrdinalComparison.SourceTypedPortsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceProof
open Source Source.ForwardTranslation Source.SourceClasses PolynomialGraphCompletion

private theorem raw_index_bound {Γ : List Ty} (c : OrdinalComponent Γ) :
    SourceCode.rawIndex c < Γ.length :=
  SourceTypedPortsProof.typedVariableIndex.1 Γ c.1 c.2.1

private theorem scalar_fresh {Γ : List Ty} (s : Scalar (OrdinalComponent Γ)) :
    Fresh Γ.length (scalarExpr SourceCode.rawIndex s) := by
  intro i hi
  rw [ScalarProof.exactOriginalNames] at hi
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hi
  exact raw_index_bound c

private theorem compiled_scalar {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c) :
    compileScalar (v 0) = some c.scalar := by
  obtain ⟨s, hs, p, _, he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, AdmissibleAssignment.collect n (fun j => extractPositive (v j.succ)) = some p ∧
        (CompiledVector.mk s p) = c := by
    simpa only [compileVector, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
  subst c
  exact hs

/-- The head class belongs to the very scalar returned by the actual vector
compiler, identified through the common deterministic assignment. -/
private theorem compiled_polynomial {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    {τ : Ty} (t : OriginalTerm Γ τ) (ht : InternalLevelBound 2 t)
    (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)
    (hc : compileVector v = some c) : PolynomialScalar c.scalar := by
  obtain ⟨w, hw, s, hs, hh⟩ :=
    Source.SourceClasses.actualSourceClasses.2 Γ hΓ τ OrdinalSyntax.defaultPolicy t ht
  rw [hv] at hw
  cases Option.some.inj hw
  have he : s = c.scalar := Option.some.inj (hs.symm.trans (compiled_scalar v c hc))
  subst s
  exact hh

theorem positive_flag {ι : Type} {k l : Nat} (index : ι → Nat) (mode : Nat)
    (a : CompiledVector ι k) (b : CompiledVector ι l) :
    SourceCode.positiveFlag mode (a.syntaxCode index) (b.syntaxCode index) = true ↔
      (if mode = 0 then ∀ j, positiveNoteAt a.positiveNotes j ≤ positiveNoteAt b.positiveNotes j
       else if mode = 1 then ∀ j, positiveNoteAt a.positiveNotes j ≤ positiveNoteAt b.positiveNotes j
       else ∀ j, positiveNoteAt a.positiveNotes j = positiveNoteAt b.positiveNotes j) := by
  unfold SourceCode.positiveFlag
  rw [GroundPositiveQuerySplit.Proof.normalized_positive,
    GroundPositiveQuerySplit.Proof.normalized_positive]
  split
  · exact positiveComparisonSourceCorrect _ _
  · split
    · exact positiveComparisonSourceCorrect _ _
    · rw [Bool.and_eq_true, positiveComparisonSourceCorrect a.positiveNotes b.positiveNotes,
        positiveComparisonSourceCorrect b.positiveNotes a.positiveNotes]
      constructor
      · rintro ⟨hab, hba⟩ j
        exact le_antisymm (hab j) (hba j)
      · intro he
        exact ⟨fun j => (he j).le, fun j => (he j).ge⟩

/-- Literal mode semantics, with weak positive coordinates also in WW-strict
mode and with the original zero padding in equality mode. -/
theorem source_relation {Γ : List Ty} {k l : Nat} (mode : Nat)
    (a : OrdinalVector Γ k) (b : OrdinalVector Γ l)
    (ca : CompiledVector (OrdinalComponent Γ) k)
    (cb : CompiledVector (OrdinalComponent Γ) l)
    (ha : compileVector a = some ca) (hb : compileVector b = some cb)
    (ρ : OrdinalComponent Γ → Nat) :
    (SourceCode.positiveFlag mode (ca.syntaxCode SourceCode.rawIndex)
        (cb.syntaxCode SourceCode.rawIndex) = true ∧
      Pair.valueRelation mode (ca.scalar.value ρ) (cb.scalar.value ρ)) ↔
      SourceCode.sourceRelation mode a b ρ := by
  rw [positive_flag]
  have za : sourceVectorAtValue a ρ 0 = (ca.scalar.value ρ : Ordinal) := by
    simpa [sourceVectorAtValue, ordinalVectorAt, CompiledVector.value] using
      (compiledVectorSound Γ k a ca ha ρ 0).symm
  have zb : sourceVectorAtValue b ρ 0 = (cb.scalar.value ρ : Ordinal) := by
    simpa [sourceVectorAtValue, ordinalVectorAt, CompiledVector.value] using
      (compiledVectorSound Γ l b cb hb ρ 0).symm
  have hp (j : Nat) := GroundPositiveQuerySplit.Proof.positive_field a ca ha ρ j
  have hq (j : Nat) := GroundPositiveQuerySplit.Proof.positive_field b cb hb ρ j
  unfold SourceCode.sourceRelation Pair.valueRelation
  by_cases h0 : mode = 0
  · simp only [h0, if_true, SourceComparisonAt, Bool.false_eq_true, if_false,
      za, zb, Nat.cast_le, hp, hq]
  · by_cases h1 : mode = 1
    · simp only [h1, Nat.one_ne_zero, if_false, if_true, SourceComparisonAt,
        za, zb, Nat.cast_lt, hp, hq]
    · simp only [h0, h1, if_false]
      constructor
      · rintro ⟨hpos, hzero⟩ j
        cases j with
        | zero => rw [za, zb, hzero]
        | succ j => simpa only [hp, hq] using hpos j
      · intro h
        refine ⟨fun j => ?_, ?_⟩
        · simpa only [hp, hq] using h (j+1)
        · simpa only [za, zb, Nat.cast_inj] using h 0

theorem actualLevelTwoCounterexamples : SourceTargets.ActualLevelTwoCounterexamples := by
  intro Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av, hav, ac, hac, _⟩ :=
    actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy a
  obtain ⟨bv, hbv, bc, hbc, _⟩ :=
    actualSourceVectorCompilation Γ hΓ υ OrdinalSyntax.defaultPolicy b
  let ae := scalarExpr SourceCode.rawIndex ac.scalar
  let be := scalarExpr SourceCode.rawIndex bc.scalar
  let flag := SourceCode.positiveFlag mode (ac.syntaxCode SourceCode.rawIndex)
    (bc.syntaxCode SourceCode.rawIndex)
  have hae : ValidExpr ae := ScalarProof.validPolynomialExpression _ _ _
    (compiled_polynomial hΓ a hla av ac hav hac)
  have hbe : ValidExpr be := ScalarProof.validPolynomialExpression _ _ _
    (compiled_polynomial hΓ b hlb bv bc hbv hbc)
  have hfa : Fresh Γ.length ae := scalar_fresh ac.scalar
  have hfb : Fresh Γ.length be := scalar_fresh bc.scalar
  have hva (ν : Nat → Nat) : ae.value ν = ac.scalar.value (fun c => ν (SourceCode.rawIndex c)) :=
    ScalarProof.exactScalarValue (OrdinalComponent Γ) SourceCode.rawIndex ac.scalar ν
  have hvb (ν : Nat → Nat) : be.value ν = bc.scalar.value (fun c => ν (SourceCode.rawIndex c)) :=
    ScalarProof.exactScalarValue (OrdinalComponent Γ) SourceCode.rawIndex bc.scalar ν
  refine ⟨av, bv, Pair.package Γ.length mode flag ae be, hav, hbv, ?_, ?_⟩
  · unfold SourceCode.compile
    rw [GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ a av ac hav hac,
      GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ b bv bc hbv hbc]
    simp only [Option.bind_some]
    change some (Pair.Code.package (Γ.length, mode, flag,
      ScalarCode.lowerSyntax (scalarSyntaxCode SourceCode.rawIndex ac.scalar),
      ScalarCode.lowerSyntax (scalarSyntaxCode SourceCode.rawIndex bc.scalar))) =
        some (Pair.package Γ.length mode flag ae be)
    rw [(ScalarCodeProof.literalScalarCode _ SourceCode.rawIndex ac.scalar).2,
      (ScalarCodeProof.literalScalarCode _ SourceCode.rawIndex bc.scalar).2,
      PairCodeProof.literalNumericPackage]
  · rw [PairProof.exactCounterexample Γ.length mode flag ae be hae hbe hfa hfb]
    constructor
    · rintro ⟨ν, hν, hbad⟩
      refine ⟨fun c => ν (SourceCode.rawIndex c),
        fun c => hν _ (raw_index_bound c), ?_⟩
      intro hs
      apply hbad
      have h := (source_relation mode av bv ac bc hac hbc
        (fun c => ν (SourceCode.rawIndex c))).mpr hs
      rw [hva ν, hvb ν]
      exact h
    · rintro ⟨ρ, hρ, hbad⟩
      obtain ⟨xs, _, hxs⟩ := groundPositiveTupleComplete Γ hΓ ρ hρ
      let ν : Nat → Nat := fun i => xs.getD i 0 + 1
      have hρν : (fun c => ν (SourceCode.rawIndex c)) = ρ := by
        funext c
        exact hxs c
      refine ⟨ν, fun _ _ => Nat.zero_lt_succ _, ?_⟩
      intro h
      apply hbad
      apply (source_relation mode av bv ac bc hac hbc ρ).mp
      rw [hva ν, hvb ν, hρν] at h
      exact h

end LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceProof

module

public import LogicLineages.ComputabilityKnowledge.PredictionSecondJumpTargets
public import LogicLineages.ComputabilityKnowledge.OraclePiTwoProof
public import LogicLineages.ComputabilityKnowledge.PredictionProgramMatricesProof
public import LogicLineages.ComputabilityKnowledge.PredictionRelativeSelectionProof
public import LogicLineages.ComputabilityKnowledge.PredictionMaximumProof
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListProof
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSecondJumpProof
open PredictionLearning PredictionCanonicalList PredictionRelativeSelection PredictionMaximum
open PredictionSecondJump PredictionSecondJumpTargets PredictionProgramMatrices OraclePiTwo

private theorem pr_codeAt : Primrec codeAt := Primrec.ofNat Code

theorem secondJumpTotalityDecision : SecondJumpTotalityDecision := by
  classical
  let matrix : Nat × Nat × Nat → Bool := fun z => totalMatrix (codeAt z.1) z.2.1 z.2.2
  have hm : Primrec matrix := PredictionProgramMatricesProof.primitiveRecursiveTotalMatrix.comp
    ((pr_codeAt.comp Primrec.fst).pair Primrec.snd)
  have h := OraclePiTwoProof.actualPiTwoSecondJumpDecision matrix hm
  apply h.of_eq
  intro i
  change Part.some (if ∀ x, ∃ y, totalMatrix (codeAt i) x y = true then 1 else 0) =
    Part.some (if TotalNat (codeAt i) then 1 else 0)
  rw [← PredictionProgramMatricesProof.exactTotalityMatrix (codeAt i)]

theorem secondJumpEqualityDecision : SecondJumpEqualityDecision := by
  classical
  let matrix : Nat × Nat × Nat → Bool := fun z =>
    equalityMatrix (codeAt z.1.unpair.1) (codeAt z.1.unpair.2) z.2.1 z.2.2
  have hleft : Primrec (fun z : Nat × Nat × Nat => codeAt z.1.unpair.1) := pr_codeAt.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
  have hright : Primrec (fun z : Nat × Nat × Nat => codeAt z.1.unpair.2) := pr_codeAt.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
  have hm : Primrec matrix := PredictionProgramMatricesProof.primitiveRecursiveEqualityMatrix.comp
    ((hleft.pair hright).pair Primrec.snd)
  have h := OraclePiTwoProof.actualPiTwoSecondJumpDecision matrix hm
  apply h.of_eq
  intro i
  change Part.some (if ∀ x, ∃ y, equalityMatrix (codeAt i.unpair.1) (codeAt i.unpair.2) x y = true then 1 else 0) =
    Part.some (if SameFunction (codeAt i.unpair.1) (codeAt i.unpair.2) then 1 else 0)
  rw [← PredictionProgramMatricesProof.exactExtensionalEqualityMatrix (codeAt i.unpair.1) (codeAt i.unpair.2)]

theorem secondJumpCanonicalSelection : SecondJumpCanonicalSelection := by
  apply PredictionRelativeSelectionProof.relativeCanonicalSelection.subst
  intro f hf
  simp only [selectionOracles, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · exact secondJumpTotalityDecision
  · exact secondJumpEqualityDecision

private def appendEncoded (z : Nat) : Nat :=
  Encodable.encode (((Encodable.decode (α := List Code) z.unpair.2).getD []) ++ [codeAt z.unpair.1])

private theorem pr_appendEncoded : Primrec appendEncoded := by
  have hi : Primrec (fun z : Nat => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun z : Nat => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hl := Primrec.option_getD.comp (Primrec.decode.comp hv) (Primrec.const ([] : List Code))
  have hc := pr_codeAt.comp hi
  have hlist := Primrec.list_concat.comp hl hc
  have h := Primrec.encode.comp hlist
  exact h.of_eq (fun _ => rfl)

private theorem prefix_succ (n : Nat) : canonicalPrefix (n + 1) = canonicalPrefix n ++ [canonicalCode n] := by
  simp [canonicalPrefix, List.range_succ]

theorem secondJumpCanonicalPrefix : SecondJumpCanonicalPrefix := by
  have hj : ComputableIn secondJumpOracles (fun z : Nat => z.unpair.2.unpair.1) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).computableIn
  have hv : ComputableIn secondJumpOracles (fun z : Nat => z.unpair.2.unpair.2) :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).computableIn
  have hindex := OracleRelativeRecursionProof.relativeComposition _ _ _ secondJumpCanonicalSelection hj
  have hargs := OracleRelativeRecursionProof.relativeNumericPairing _ _ _ hindex hv
  have hstep := OracleRelativeRecursionProof.relativeComposition _ _ _ pr_appendEncoded.computableIn hargs
  let step : Nat → Nat := fun z => appendEncoded
    (Nat.pair (canonicalIndex z.unpair.2.unpair.1) z.unpair.2.unpair.2)
  have hs : ComputableIn secondJumpOracles step := hstep
  have ht := OracleRelativeRecursionProof.relativePrimitiveRecursion secondJumpOracles
    (fun _ => Encodable.encode ([] : List Code)) step (Primrec.const _).computableIn hs
  have he : ∀ a n, OracleRelativeRecursion.parameterRec (fun _ => Encodable.encode ([] : List Code)) step
      (Nat.pair a n) = Encodable.encode (canonicalPrefix n) := by
    intro a n
    simp only [OracleRelativeRecursion.parameterRec, Nat.unpair_pair]
    induction n with
    | zero => rfl
    | succ n ih =>
        change step (Nat.pair a (Nat.pair n (Nat.rec (Encodable.encode ([] : List Code))
          (fun j previous => step (Nat.pair a (Nat.pair j previous))) n))) = _
        rw [ih]
        simp only [step, appendEncoded, Nat.unpair_pair, Encodable.encodek, Option.getD_some,
          prefix_succ, canonicalCode]
  have hin : ComputableIn secondJumpOracles (fun n => Nat.pair 0 n) :=
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).computableIn
  have h := OracleRelativeRecursionProof.relativeComposition _ _ _ ht hin
  apply h.of_eq
  intro n
  exact congrArg Part.some (he 0 n)

theorem uniformSecondJumpMaximumIndices : UniformSecondJumpMaximumIndices := by
  obtain ⟨universal, hcomp, hsem, _⟩ := PredictionMaximumProof.uniformMaximumCompiler
  have hdecode : Computable (fun z : Nat => (Encodable.decode (α := List Code) z).getD []) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const [])).to_comp
  have hc : Computable (fun z : Nat => Encodable.encode (compileMaximum universal
      ((Encodable.decode (α := List Code) z).getD []))) :=
    Primrec.encode.to_comp.comp (hcomp.comp hdecode)
  have h := OracleRelativeRecursionProof.relativeComposition _ _ _ hc.computableIn secondJumpCanonicalPrefix
  have hindex : ComputableIn secondJumpOracles (compiledBoundIndex universal) := by
    apply h.of_eq
    intro m
    simp only [Encodable.encodek, Option.getD_some, compiledBoundIndex]
  refine ⟨universal, hsem, hindex, ?_⟩
  intro m hm
  simpa only [compiledBoundIndex, Denumerable.ofNat_encode] using
    PredictionMaximumProof.canonicalOrdinaryBounds universal hsem m hm

theorem fullCanonicalList : FullCanonicalList := by
  refine ⟨secondJumpCanonicalSelection, PredictionCanonicalListProof.strictCanonicalEnumeration.1,
    ?_, PredictionCanonicalListProof.exhaustiveCanonicalCodes,
    PredictionCanonicalListProof.exhaustiveTotalComputableFunctions, uniformSecondJumpMaximumIndices⟩
  intro n
  have h := PredictionCanonicalListProof.strictCanonicalEnumeration.2 n
  exact ⟨h, h.1⟩

end LogicLineages.ComputabilityKnowledge.PredictionSecondJumpProof

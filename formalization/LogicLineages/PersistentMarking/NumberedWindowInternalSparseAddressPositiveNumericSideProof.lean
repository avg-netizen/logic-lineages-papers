module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSlotsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSideProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (contextView typeBit)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (literalFields)
open NumberedWindowInternalSparsePositiveFoldTargets (ActualPositiveCalibration packedPositive)
open NumberedWindowInternalSparseAddressPositive
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
open NumberedWindowInternalSparseAddressPositiveNumericShapeProof
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof

theorem fields {q : Nat} (d : Decoded q) :
    run rawContext q = d.ctx ∧ run rawResult q = d.ty ∧ run rawLeast q = d.classCode := by
  obtain ⟨a,b,c⟩ := literalFields d.ctx d.ty d.classCode
  exact ⟨(congrArg (run rawContext) d.nameEq).trans a,
    (congrArg (run rawResult) d.nameEq).trans b,
    (congrArg (run rawLeast) d.nameEq).trans c⟩

theorem reportsOf {cv tv : Program 1} (hc : ActualContextGuard cv) (ht : ActualTypeGuard tv)
    {q : Nat} (d : Decoded q) : sideReports cv tv q := by
  obtain ⟨a,b,_⟩ := fields d
  refine ⟨(shape q).mpr ⟨d.ctx,d.ty,d.classCode,d.nameEq⟩,?_⟩
  rw [a,b]
  change evaluate cv (d.ctx ::ᵥ nil) = 1 ∧ evaluate tv (d.ty ::ᵥ nil) = 1
  simp [hc d.ctx,ht d.ty,d.contextOk,d.typeOk]

theorem decodedOf {cv tv : Program 1} (hc : ActualContextGuard cv) (ht : ActualTypeGuard tv)
    {q : Nat} (side : sideReports cv tv q) : Nonempty (Decoded q) := by
  obtain ⟨c,t,k,h⟩ := (shape q).mp side.1
  have f1 : run rawContext q = c := by rw [h]; exact (literalFields c t k).1
  have f2 : run rawResult q = t := by rw [h]; exact (literalFields c t k).2.1
  obtain ⟨ctx,type⟩ := side.2
  rw [f1] at ctx
  rw [f2] at type
  change evaluate cv (c ::ᵥ nil) = 1 at ctx
  change evaluate tv (t ::ᵥ nil) = 1 at type
  rw [hc c] at ctx
  rw [ht t] at type
  have ty : typeBit t = true := by
    cases e : typeBit t <;> simp_all
  cases e : contextView c with
  | none => simp [e] at ctx
  | some stack => exact ⟨⟨c,t,k,stack,h,e,ty⟩⟩

theorem coreOf {entries : Entries} {s : Settings} {raw : Program 5} {least : Program 3}
    (cal : ActualPositiveCalibration entries s raw least)
    {x y : Nat} (w : Nat) (l : Decoded x) (r : Decoded y) :
    evaluate (callFold raw least) (tape x w y) = 1 ↔
      NumberedWindowPositivePathAlgorithm.positive (NumberedWindowConcreteCheckers.step entries s)
        (NumberedWindowScalarAlgorithm.least s) l.stack l.ty l.classCode w r.classCode = true := by
  obtain ⟨lc,lt,ls⟩ := fields l
  have rd := (fields r).2.2
  rw [foldCall,lc,lt,ls,rd,cal l.ctx l.ty l.classCode w r.classCode]
  unfold packedPositive
  rw [unpackContext l.contextOk]
  simp only [Option.any_some]
  split <;> simp_all

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSideProof

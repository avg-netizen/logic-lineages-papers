module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LayeredComparison.SnyatkovCompletion
open OriginalWordEvaluation.Proof

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem variables_calibration (p : Formula) : Code.variables (Formula.encode p) = p.variables := by
  simp only [Code.variables,wordAtomsCalibration,List.flatMap_map,Function.comp_def,
    wordDecodeAtomData,atomDataRow,Formula.variables,Formula.tokens,List.map_flatMap,
    List.map_map,rowVariables]

theorem names_calibration (p : Formula) : Code.names (Formula.encode p) = names p := by
  rw [Code.names,variables_calibration]
  rfl

theorem residueAtom_calibration (a : Atom) : Code.residueAtom a.data = (residueAtom a).data := by
  cases a <;> simp [Code.residueAtom,residueAtom,Atom.data]

theorem residue_calibration (p : Formula) :
    Code.residue (Formula.encode p) = Formula.encode (residue p) := by
  unfold Code.residue
  induction p with
  | bot =>
      simpa [Formula.encode,residue] using wordMapAtomsStep
        (fun payload => Encodable.encode (Code.residueAtom
          (WordLinearDecisionCompletion.Code.decodeAtom payload))) 0 1 (by decide)
  | top =>
      simpa [Formula.encode,residue] using wordMapAtomsStep
        (fun payload => Encodable.encode (Code.residueAtom
          (WordLinearDecisionCompletion.Code.decodeAtom payload))) 0 0 (by decide)
  | atom a =>
      simpa [Formula.encode,residue,wordDecodeAtomData,residueAtom_calibration] using wordMapAtomsStep
        (fun payload => Encodable.encode (Code.residueAtom
          (WordLinearDecisionCompletion.Code.decodeAtom payload)))
        (Encodable.encode a.data) 2 (by decide)
  | neg p ih =>
      simpa [Formula.encode,residue,ih] using wordMapAtomsStep
        (fun payload => Encodable.encode (Code.residueAtom
          (WordLinearDecisionCompletion.Code.decodeAtom payload))) (Formula.encode p) 3 (by decide)
  | conj p q ihp ihq =>
      simpa [Formula.encode,residue,Nat.unpair_pair,ihp,ihq] using wordMapAtomsStep
        (fun payload => Encodable.encode (Code.residueAtom
          (WordLinearDecisionCompletion.Code.decodeAtom payload)))
        (Nat.pair (Formula.encode p) (Formula.encode q)) 4 (by decide)
  | disj p q ihp ihq =>
      simpa [Formula.encode,residue,Nat.unpair_pair,ihp,ihq] using wordMapAtomsStep
        (fun payload => Encodable.encode (Code.residueAtom
          (WordLinearDecisionCompletion.Code.decodeAtom payload)))
        (Nat.pair (Formula.encode p) (Formula.encode q)) 5 (by decide)

theorem residueTail_calibration (p : Formula) :
    Code.residueTail (Formula.encode p) = residueTail p := by
  simp only [Code.residueTail,wordAtomsCalibration,List.map_map,Function.comp_def,
    wordDecodeAtomData,residueTail]
  congr 2
  funext a
  cases a <;> simp [Atom.data,residueAtomTail]

theorem frame_calibration (N maximum : Nat) (ns : List Nat) :
    Code.frame N maximum ns = Formula.encode (frame N maximum ns) := by
  induction ns with
  | nil => rfl
  | cons i ns ih =>
      simp only [Code.frame,frame,List.foldr_cons,LinearRows.Code.conjunction,
        Formula.encode,Code.nonnegative,Atom.data] at ih ⊢
      rw [ih]

theorem initial_calibration (p : Formula) :
    Code.variables (Formula.encode p) = p.variables ∧
    Code.names (Formula.encode p) = names p ∧
    Code.residue (Formula.encode p) = Formula.encode (residue p) ∧
    Code.residueTail (Formula.encode p) = residueTail p :=
  ⟨variables_calibration p,names_calibration p,residue_calibration p,residueTail_calibration p⟩

#print axioms variables_calibration
#print axioms names_calibration
#print axioms residueAtom_calibration
#print axioms residue_calibration
#print axioms residueTail_calibration
#print axioms frame_calibration
#print axioms initial_calibration

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeProof

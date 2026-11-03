module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCodeSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Proof
open BalancedSyntax BalancedEvaluation

private theorem getDOfFn {A : Type} {k : Nat} (f : Fin k → A) (d : A)
    (j : Nat) (hj : j < k) : (List.ofFn f).getD j d = f ⟨j,hj⟩ := by
  rw [List.getD_eq_getElem _ d (by simpa using hj)]
  simp only [List.getElem_ofFn]

private theorem mapRangeFin {A : Type} (k : Nat) (f : Nat → A) (g : Fin k → A)
    (h : ∀ j (hj : j < k), f j = g ⟨j,hj⟩) :
    (List.range k).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact h i (by simpa using hi)

/-- Calibration uses the existing raw norm of the actual normal head. -/
private theorem actualNorm (h : NONote) :
    rawNormCode (rawNoteEncode h.1) = actualOrdinalNorm h.1.repr :=
  (rawNormCodeCorrect h.1).trans (actualOrdinalNorm_notationCorrespondence h).symm

/-- The stored factor is incremented at every common-basis position. -/
private theorem encodedFactors {k : Nat} (a : Nat × Atom k) :
    factors k (encodeAtom a) = (asAtom a.2).coefficients := by
  unfold factors encodeAtom asAtom
  dsimp only
  apply mapRangeFin
  intro j hj
  rw [getDOfFn _ _ j hj]

private theorem encodedOffset {k : Nat} (a : Nat × Atom k) :
    normOffset (encodeAtom a) = BalancedRow.normOffset (asAtom a.2) := by
  simp only [normOffset,encodeAtom,BalancedRow.normOffset,asAtom,actualNorm]

private theorem originalAtoms {k : Nat} (Γ : List Nat) (E F : Upper k) :
    upperAtoms (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      (E.atoms ++ F.atoms).map encodeAtom := by
  simp only [upperAtoms,upperData,encodeSyntax,Encodable.encodek,
    Option.getD_some,List.map_append]

private theorem originalCoefficients {k : Nat} (Γ : List Nat) (E F : Upper k) :
    coefficients (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedLargeGuards.sourceCoefficients E F := by
  simp only [coefficients,upperData,encodeSyntax,Encodable.encodek,
    Option.getD_some,BalancedLargeGuards.sourceCoefficients,
    BalancedLargeGuards.signedAtoms,List.map_append,List.map_map,
    Function.comp_def,encodeAtom]

private theorem originalHeads {k : Nat} (Γ : List Nat) (E F : Upper k) :
    headCodes (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedLargeGuardsCode.encodeHeads
        ((BalancedLargeGuards.signedAtoms E F).map (fun a => a.2.head)) := by
  simp only [headCodes,originalAtoms,BalancedLargeGuardsCode.encodeHeads,
    BalancedLargeGuards.signedAtoms,List.map_append,List.map_map,
    Function.comp_def,encodeAtom]

private theorem originalConstantExact {k : Nat} (Γ : List Nat) (E F : Upper k) :
    originalConstant (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      (comparisonRow E F).constant := by
  simp only [originalConstant,upperData,encodeSyntax,Encodable.encodek,
    Option.getD_some,comparisonRow]

private theorem originalOutside {k : Nat} (Γ : List Nat) (E F : Upper k) :
    outsideCoefficients k (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      (comparisonRow E F).remainder := by
  simp only [outsideCoefficients,upperData,encodeSyntax,Encodable.encodek,
    Option.getD_some,comparisonRow]
  apply mapRangeFin
  intro j hj
  rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]

private theorem originalMass {k : Nat} (Γ : List Nat) (E F : Upper k) :
    coefficientMass (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedRow.coefficientMass (comparisonRow E F) := by
  simp only [coefficientMass,originalCoefficients,
    BalancedLargeGuards.sourceCoefficients,BalancedLargeGuards.signedAtoms,
    BalancedRow.coefficientMass,comparisonRow,List.map_append,List.map_map,
    Function.comp_def]

private theorem originalOutsideMaximum {k : Nat} (Γ : List Nat) (E F : Upper k) :
    outsideMaximum k (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedRow.outsideMaximum (comparisonRow E F) := by
  simp only [outsideMaximum,originalOutside,BalancedRow.outsideMaximum]

private theorem originalMultiplierMaximum {k : Nat} (Γ : List Nat) (E F : Upper k) :
    multiplierMaximum k (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedRow.multiplierMaximum (comparisonRow E F) := by
  simp only [multiplierMaximum,originalAtoms,BalancedRow.multiplierMaximum,
    comparisonRow,List.flatMap_map,List.flatMap_append,encodedFactors]

private theorem originalOffsetMaximum {k : Nat} (Γ : List Nat) (E F : Upper k) :
    offsetMaximum (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedRow.offsetMaximum (comparisonRow E F) := by
  simp only [offsetMaximum,originalAtoms,BalancedRow.offsetMaximum,
    comparisonRow,List.map_append,List.map_map,Function.comp_def,encodedOffset]

private theorem originalNormMaximum {k : Nat} (Γ : List Nat) (E F : Upper k) :
    normMaximum (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedRow.normMaximum (comparisonRow E F) := by
  simp only [normMaximum,headCodes,originalAtoms,BalancedRow.normMaximum,
    comparisonRow,List.map_append,List.map_map,Function.comp_def,encodeAtom,
    asAtom,actualNorm]

private theorem originalThreshold {k : Nat} (Γ : List Nat) (E F : Upper k) :
    threshold k (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      BalancedRow.threshold (comparisonRow E F) := by
  simp only [threshold,BalancedRow.threshold,originalConstantExact,originalMass,
    originalOutsideMaximum,originalMultiplierMaximum,originalOffsetMaximum,
    originalNormMaximum]

/-- All metadata and budgets belong to the original occurrence lists, before
any cancellation or collection, with complete ordered atom payloads intact. -/
theorem exactOriginalMetadata : Targets.ExactOriginalMetadata := by
  intro k Γ E F
  exact ⟨originalAtoms Γ E F,originalCoefficients Γ E F,originalHeads Γ E F,
    originalConstantExact Γ E F,originalOutside Γ E F,originalMass Γ E F,
    originalOutsideMaximum Γ E F,originalMultiplierMaximum Γ E F,
    originalOffsetMaximum Γ E F,originalNormMaximum Γ E F,originalThreshold Γ E F⟩

private theorem literalLowerCertificate (k : Nat) (Γ : List Nat)
    (C : Certificate (k::Γ)) :
    lowerCertificate (encodeCertificate (k::Γ) C) = encodeCertificate Γ C.1 := by
  simp only [lowerCertificate,encodeCertificate,certificateData,
    Encodable.encodek,Option.getD_some]

private theorem literalTerms (k : Nat) (Γ : List Nat)
    (C : Certificate (k::Γ)) (E F : Upper k) :
    termCodes k Γ (encodeCertificate (k::Γ) C)
        (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
      (BalancedLargeGuards.sourceTerms k Γ C E F).map (encodeSyntax Γ) := by
  have hi (a : Nat × Atom k) :
      BalancedAffineCode.completeInput k Γ (encodeCertificate (k::Γ) C)
          (Encodable.encode (encodeAtom a)) =
        encodeSyntax Γ (Affine.completeInput k Γ C a.2) :=
    (BalancedAffineCode.Proof.exactActualLowerAndInputs k Γ C E a.2 a.1).2
  have hl (G : Upper k) :
      BalancedAffineCode.lowerPart k Γ (encodeCertificate (k::Γ) C)
          (encodeSyntax (k::Γ) G) = encodeSyntax Γ (Affine.lowerPart k Γ C G) := by
    -- An empty basis or atom list is permitted; the supplier's atom parameter
    -- is used only to project its independent lower-part equality.
    let a : Atom k := ⟨0,0,fun _ => 0⟩
    exact (BalancedAffineCode.Proof.exactActualLowerAndInputs k Γ C G a 0).1
  simp only [termCodes,originalAtoms,BalancedLargeGuards.sourceTerms,
    BalancedLargeGuards.signedAtoms,List.map_append,List.map_map,
    Function.comp_def,List.map_cons,List.map_nil,hi,hl]

/-- Every complete input and both final outside terms use the actual lower
certificate, including at the empty lower shape. -/
theorem exactLiteralSourceLabels : Targets.ExactLiteralSourceLabels := by
  intro k Γ C E F
  exact ⟨literalLowerCertificate k Γ C,literalTerms k Γ C E F⟩

attribute [local irreducible] BalancedLargeGuardsCode.largeCode
  BalancedLargeGuards.largeFormula CommonHeadCompiler.encode

private theorem literalFormula {k : Nat} (Γ : List Nat) (E F : Upper k)
    (desired : Int) :
    formulaCode k (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) desired =
      CommonHeadCompiler.encode (BalancedLargeGuards.sourceFormula E F desired) := by
  unfold formulaCode BalancedLargeGuards.sourceFormula BalancedLargeGuards.sourceHeads
  rw [originalThreshold,originalHeads,originalCoefficients]
  exact BalancedLargeGuardsCode.Proof.exactLargeGuardCode.2.2
    (BalancedRow.threshold (comparisonRow E F))
    ((BalancedLargeGuards.signedAtoms E F).map (fun a => a.2.head))
    (BalancedLargeGuards.sourceCoefficients E F) desired

/-- Assembly is the existing source formula's literal postfix encoding with
its original ordered labels and the original certificate's lower component. -/
theorem exactAssembledSourceCode : Targets.ExactAssembledSourceCode := by
  intro k Γ C E F desired
  refine ⟨literalFormula Γ E F desired,?_⟩
  simp only [assemble,literalLowerCertificate,literalTerms,literalFormula]

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Proof

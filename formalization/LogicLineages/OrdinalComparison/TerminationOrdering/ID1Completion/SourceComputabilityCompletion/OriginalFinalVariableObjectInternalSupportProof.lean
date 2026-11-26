module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectWrapperSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectInternalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaFinalLogicProof
open OriginalRawObjectTransport OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Functionality and equality elimination characterize every output once
an actual value graph has been constructed. -/
theorem valueEquation {n : Nat} (p : Program n) (out value : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph p value xs))) :
    Nonempty (Derivation body Delta ((programGraph p out xs).iff (equal out value))) := by
  let A := programGraph p out xs
  let B := equal out value
  obtain ⟨hf⟩ := valueUnique p out value xs
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (addAssumption hv A)
  have he : Derivation body (B :: Delta) (eqn out value) := by
    simpa only [B,equalEqn] using
      (Derivation.hypothesis List.mem_cons_self : Derivation body (B :: Delta) B)
  obtain ⟨hb⟩ := outputTransport p value out xs ⟨symm he⟩ (addAssumption hv B)
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (by simpa only [equalEqn] using hf))
    (Derivation.implicationIntroduction hb)⟩

/-- Change only the Object input; the outer Context remains identical. -/
theorem secondTransport (p : Program 2) (out first source target : OTerm alpha)
    (he : Nonempty (Derivation body Delta (equal source target)))
    (hg : Nonempty (Derivation body Delta (graph2 p out first source))) :
    Nonempty (Derivation body Delta (graph2 p out first target)) := by
  apply graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons first (Fin.cons source Fin.elim0)) (Fin.cons first (Fin.cons target Fin.elim0)) _ hg
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · rw [onEquality]; exact ⟨refl first⟩
  · rw [onEquality]
    exact (show Nonempty (Derivation body Delta (eqn source target)) from
      by simpa only [equalEqn] using he)

/-- Symbolic equality transports both directions of the original rank graph. -/
theorem unaryInputEquation (p : Program 1) (out source target : OTerm alpha)
    (he : Nonempty (Derivation body Delta (equal source target))) :
    Nonempty (Derivation body Delta ((graph1 p out source).iff (graph1 p out target))) := by
  let A := graph1 p out source
  let B := graph1 p out target
  obtain ⟨he'⟩ := he
  have heq : Derivation body Delta (eqn source target) := by simpa only [equalEqn] using he'
  obtain ⟨hf⟩ := headTransport p out source target Fin.elim0 (addAssumption ⟨heq⟩ A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := headTransport p out target source Fin.elim0 (addAssumption ⟨symm heq⟩ B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- An actual arbitrary Object shift output has the same extended context
and shifted payload supplied by the actual cons and packed-shift graphs.
No shape is imposed on that output as an extra premise. -/
theorem shiftObjectPair (d input out gamma raw extendedGamma shifted : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extendedGamma d gamma)))
    (ht : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.shiftPackedRaw shifted (numeral 0) raw)))
    (ho : Nonempty (Derivation body Delta (graph2 shiftObjectRaw out d input))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out extendedGamma shifted)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons d (Fin.cons input Fin.elim0)
  have hl := unaryValue InternalUnpair.left (.projection 1) gamma input xs
    (pairLeft input gamma raw hp) (projectionValue 1 xs)
  have hr := unaryValue InternalUnpair.right (.projection 1) raw input xs
    (pairRight input gamma raw hp) (projectionValue 1 xs)
  have hext := binaryValue InternalListCodec.consCode (.projection 0) (leftOf (.projection 1))
    extendedGamma d gamma xs hc (projectionValue 0 xs) hl
  have hshift := binaryValue OriginalRawSyntaxTransport.shiftPackedRaw (constant 2 0) (rightOf (.projection 1))
    shifted (numeral 0) raw xs ht (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xs) hr
  exact binaryRecover InternalPairing.pairing
    (consOf (.projection 0) (leftOf (.projection 1)))
    (.composition OriginalRawSyntaxTransport.shiftPackedRaw ![constant 2 0,rightOf (.projection 1)])
    out extendedGamma shifted xs ho hext hshift

/-- Object rank reads the literal right coordinate of the actual Object pair,
then the independently accepted raw variable rank branch. -/
theorem objectVariableRankEquation (out input gamma raw variableCode typ index : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw typ variableCode))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw out input).iff (equal out (numeral 1)))) := by
  have hobject := OriginalFinalVariableWeakeningSupportProof.compositionEquation
    OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => InternalUnpair.right)
    out (Fin.cons input Fin.elim0) (Fin.cons raw Fin.elim0)
    (fun i => Fin.cases (pairRight input gamma raw hp) (fun j => Fin.elim0 j) i)
  exact iffCompose hobject
    (OriginalFinalVariableCanonicalRawProof.packedVariableRankEquation out raw variableCode typ index hc hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectInternalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectInternalSupportProof

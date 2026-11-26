module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectExposureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalTypedDecoderInternalScalarProof (pairRightValue)
open OriginalFinalVariableObject OriginalFinalVariableObjectWrapperSupportProof
open InternalParameterizedCanonicalResultFold (foldGraph foldN)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Actual exposure wiring with already named input coordinates and actual
fold output. All bookkeeping comes from original pair graphs. -/
theorem outputPair (p : GlobalSourcePackage.Inputs)
 (context input out gamma raw parameter canonicalRaw : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hf : Nonempty (Derivation body Delta (foldGraph (OriginalLambdaTraversalSelection.finalData p) canonicalRaw raw parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (canonicalObjectProgram p) out context input))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out gamma canonicalRaw)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons context (Fin.cons input Fin.elim0)
 have hl := unaryValue InternalUnpair.left (.projection 1) gamma input xs
   (pairLeft input gamma raw hp) (projectionValue 1 xs)
 have hr := unaryValue InternalUnpair.right (.projection 1) raw input xs
   (pairRight input gamma raw hp) (projectionValue 1 xs)
 have hparam' := binaryValue InternalPairing.pairing (.projection 0) objectContext
   parameter context gamma xs hparam (projectionValue 0 xs) hl
 have hf' := binaryValue (foldN (OriginalLambdaTraversalSelection.finalData p))
   objectPayload objectParameter canonicalRaw raw parameter xs hf hr hparam'
 exact binaryRecover InternalPairing.pairing objectContext (canonicalPayload p)
   out gamma canonicalRaw xs ho hl hf'
theorem equalPairs (leftOut rightOut gamma leftRaw rightRaw : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal leftRaw rightRaw)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftOut gamma leftRaw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightOut gamma rightRaw))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 have hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftOut gamma rightRaw)) := by
   simp only [graph2,programGraph] at hl ⊢
   apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
     (OrdinaryArithmetic.graphFormula InternalPairing.pairing) leftOut ![gamma,leftRaw] ![gamma,rightRaw] _ hl
   intro i
   have hg : Nonempty (Derivation body Delta (equal gamma gamma)) := by
     rw [equalEqn]; exact ⟨InternalTagArithmeticSupportProof.refl gamma⟩
   exact Fin.cases hg (Fin.cases he (fun k => Fin.elim0 k)) i
 have hq := valueUnique InternalPairing.pairing leftOut rightOut ![gamma,rightRaw] hh hr
 exact (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn leftOut rightOut)).mpr hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectSupportProof

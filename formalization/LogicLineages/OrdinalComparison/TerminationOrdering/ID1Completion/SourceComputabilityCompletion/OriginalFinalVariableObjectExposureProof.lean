module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectWrapperSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectExposureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionTotalityProof InternalRecursionClosureProof
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalFinalVariableObject OriginalFinalVariableObjectWrapperSupportProof

/-- Totality binds every runtime coordinate inside the original calculus.
The proof is independent of native evaluation and works on all symbolic inputs. -/
theorem actualOriginalFinalVariableObjectExposure :
    OriginalFinalVariableObjectTargets.ActualOriginalFinalVariableObjectExposure := by
  intro p
  constructor
  · intro body alpha Delta context input out psi ho k
    let xs : Fin 2 → OTerm alpha := Fin.cons context (Fin.cons input Fin.elim0)
    apply supplyOutputs body 2 4 (fun i => OrdinaryArithmetic.graphFormula (wrapperQueries p i))
      (fun i => (actualOriginalPrograms body 2 (wrapperQueries p i)).1) alpha Delta xs psi
    intro beta j Theta ys hj hs
    apply k beta j Theta hj (ys 0) (ys 1) (ys 2) (ys 3)
    have ho' := binaryRename (canonicalObjectProgram p) out context input ho j Theta hj
    have hs' : ∀ i, Nonempty (Derivation body Theta
        (programGraph (wrapperQueries p i) (ys i)
          (Fin.cons (context.relabel j) (Fin.cons (input.relabel j) Fin.elim0)))) :=
      fun i => queryTwoRename (wrapperQueries p i) context input j Theta (ys i) (hs i)
    exact recoveredAt p (context.relabel j) (input.relabel j) (out.relabel j) ys hs' ho'
  · intro body alpha Delta context input out gamma raw parameter canonicalRaw h
    exact wrapperBackward p context input out gamma raw parameter canonicalRaw
      (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
      (andRight (andRight (andRight h)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectExposureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectExposureProof

module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalParameterizedApplicationResultFoldTotality
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- INTERNAL strong-payload induction result for ALL original packed inputs
and parameters. The induction step, branch inversion, strict child-payload
bounds and child certifications must be proved, not supplied as hypotheses,
fields, semantic calibration or a fixed-input induction assumption. -/
def ActualOriginalParameterizedResultFoldPayloadTotality : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (payload : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (atPayloadP guard leaf combine payload))

/-- Unconditional INTERNAL certified output existence for every original
packed input and symbolic parameter, including malformed inputs and zero
outputs. The existing runP retains its exact succ(payload+payload) fuel.
No validity, type, canonicality, member, source or calibration premise. -/
def ActualOriginalParameterizedResultFoldCertifiedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (input parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter))

/-- A consumer of the ACTUAL fold graph obtains actual whole-state H=1.
Success must follow from the proved internal totality theorem, never from
external calibration, output positivity or treating default zero as success. -/
def ActualOriginalParameterizedResultFoldOutputSuccess : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (out input parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((foldGraphP guard leaf combine out input parameter).imp
      (goodRunAcceptedP guard leaf combine input parameter)))

/-- Exact INTERNAL application fold/combine equation without supplied child
success. The original constructors and exact-one root G remain premises;
both child graphs are ACTUAL raw foldP graphs at the SAME p. C's order is
[d,e,functionOut,argumentOut,p]. No validity, canonicality, member, calibration,
output bound, nonzero-output condition or enlarged fuel is introduced. -/
def ActualOriginalParameterizedResultFoldApplicationEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α))
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph2 guard InternalOriginalStepGuard.one parent parameter ⊓
        (foldGraphP guard leaf combine functionOut fn parameter ⊓
          foldGraphP guard leaf combine argumentOut arg parameter))).imp
      ((foldGraphP guard leaf combine out parent parameter).iff
        (programGraph combine out
          (Fin.cons d (Fin.cons e (Fin.cons functionOut
            (Fin.cons argumentOut (Fin.cons parameter Fin.elim0)))))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityTargets

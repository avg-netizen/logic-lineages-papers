module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedSyntaxBoundsPrimrec
open NumberedSyntaxBoundsPrimrecSupportProof

theorem termBoundsCalibration : NumberedSyntaxBoundsPrimrecTargets.ActualTermBoundsCalibration := by
  intro Symbol arity Gamma tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => codeBounds (argumentsCode args) =
      (NumberedPrimaryEquivalence.argumentsSize args, argumentsMaxLabel args))
  all_goals simp_all [termCode, argumentsCode, codeBounds,
    NumberedPrimaryEquivalence.size, NumberedPrimaryEquivalence.argumentsSize,
    maxLabel, argumentsMaxLabel]

theorem argumentsBoundsCalibration : NumberedSyntaxBoundsPrimrecTargets.ActualArgumentsBoundsCalibration := by
  intro Symbol arity Gamma types args
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih =>
    cases args with
    | cons q rest =>
      simp [argumentsCode, codeBounds, NumberedPrimaryEquivalence.argumentsSize,
        argumentsMaxLabel, termBoundsCalibration Symbol arity Gamma sigma q, ih rest]

theorem codeBoundsPrimitive : NumberedSyntaxBoundsPrimrecTargets.ActualCodeBoundsPrimitive := by
  intro n
  exact Primrec.nat_omega_rec' (@codeBounds (Fin n))
    (m := @codeNumber n) (l := @children (Fin n)) (g := @recombine (Fin n))
    (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n)
    (childrenPrimitive n) (recombinePrimitive n)
    (childrenDecrease n) recombineCalibration

theorem packedBoundsPrimitive : NumberedSyntaxBoundsPrimrecTargets.ActualPackedBoundsPrimitive := by
  intro n arity Gamma
  have hcode : Primrec (fun q : Packed (Fin n) arity Gamma => termCode q.2) :=
    Primrec.snd.comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma)
  exact ((codeBoundsPrimitive n).comp
    (g := fun q : Packed (Fin n) arity Gamma => termCode q.2) hcode).of_eq
    (fun q : Packed (Fin n) arity Gamma =>
      termBoundsCalibration (Fin n) arity Gamma q.1 q.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecProof

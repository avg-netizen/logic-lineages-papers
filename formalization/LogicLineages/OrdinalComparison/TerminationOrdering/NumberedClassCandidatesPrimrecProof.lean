module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration
open NumberedAuxiliaryDecoding NumberedPrimaryEquivalence

private abbrev Input (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma

theorem classCodesPrimitive : NumberedClassCandidatesPrimrecTargets.ActualClassCodesPrimitive := by
  intro n arity Gamma
  have hbounds : Primrec (fun p : Input n arity Gamma => (size p.2.2, maxLabel p.2.2)) :=
    (NumberedSyntaxBoundsPrimrecProof.packedBoundsPrimitive n arity Gamma).comp Primrec.snd
  have hsize : Primrec (fun p : Input n arity Gamma => size p.2.2) := Primrec.fst.comp hbounds
  have hlabel : Primrec (fun p : Input n arity Gamma => maxLabel p.2.2) := Primrec.snd.comp hbounds
  have hheads : Primrec (fun p : Input n arity Gamma => sourceHeads arity p.1.1 p.1.2) :=
    (NumberedEnumerationOperationsPrimrecProof.sourceHeadsPrimitive n arity).comp Primrec.fst
  have hdata : Primrec (fun p : Input n arity Gamma =>
      (p.1.2, sourceHeads arity p.1.1 p.1.2, maxLabel p.2.2, size p.2.2)) :=
    (Primrec.snd.comp Primrec.fst).pair (hheads.pair (hlabel.pair hsize))
  have hlimits : Primrec (fun p : Input n arity Gamma => (Gamma.length, 2 * size p.2.2)) :=
    (Primrec.const Gamma.length).pair (Primrec.nat_mul.comp (Primrec.const 2) hsize)
  have henumerate : Primrec (fun p : Input n arity Gamma =>
      enumerate p.1.2 (sourceHeads arity p.1.1 p.1.2) (maxLabel p.2.2) (size p.2.2)
        Gamma.length (2 * size p.2.2)) :=
    (NumberedCodeEnumerationPrimrecProof.enumerationPrimitive n).comp hdata hlimits
  have htype : Primrec (fun p : Input n arity Gamma => p.2.1) :=
    Primrec.fst.comp ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp Primrec.snd)
  have hpair : Primrec (fun p : Input n arity Gamma × Code (Fin n) => (p.1.2.1, p.2)) :=
    (htype.comp Primrec.fst).pair Primrec.snd
  exact (Primrec.list_map henumerate hpair.to₂).of_eq (by intro p; rfl)

theorem classCandidatesPrimitive : NumberedClassCandidatesPrimrecTargets.ActualClassCandidatesPrimitive := by
  intro n arity Gamma
  have hdecode : Primrec (fun p : Input n arity Gamma × (Ty × Code (Fin n)) =>
      decodePacked arity Gamma p.2) :=
    (NumberedPackedStructurePrimrecProof.structuralDecoderPrimitive n arity Gamma).comp Primrec.snd
  exact (Primrec.listFilterMap (classCodesPrimitive n arity Gamma) hdecode.to₂).of_eq (by intro p; rfl)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecProof

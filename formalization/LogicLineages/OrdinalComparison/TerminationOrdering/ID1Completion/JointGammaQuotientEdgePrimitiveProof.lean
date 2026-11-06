module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientEdgePrimitiveProof
open Source NumberedUniformPackedDecoding JointGammaQuotient

attribute [local irreducible] Primrec ContextUniformPrimary.representative
  rawPackedDecode rawUniverseDecode NumberedNumericStep.numericStepTest rawEdgeTest

theorem rawEdgePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Parameters n × Nat × Nat × Nat =>
      rawEdgeTest n arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let Input := Parameters n × Nat × Nat × Nat
  have hp : Primrec (fun p : Input => p.1) := Primrec.fst
  have hw : Primrec (fun p : Input => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp hp)
  have hg : Primrec (fun p : Input => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp hp)
  have ht : Primrec (fun p : Input => p.1.2) := Primrec.snd.comp hp
  have hx : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : Input => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : Input => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hu := Primrec.unpair.comp hc
  have hs : Primrec (fun p : Input => (Nat.unpair p.2.2.2).1) := Primrec.fst.comp hu
  have hu' := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hr : Primrec (fun p : Input => (Nat.unpair (Nat.unpair p.2.2.2).2).1) := Primrec.fst.comp hu'
  have hcert : Primrec (fun p : Input => (Nat.unpair (Nat.unpair p.2.2.2).2).2) := Primrec.snd.comp hu'
  have hsource : Primrec (fun p : Input =>
      rawUniverseDecode n arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 (Nat.unpair p.2.2.2).1) :=
    (NumberedUniformPackedDecodingProof.rawUniverseDecoderPrimitive n arity).comp (hw.pair (hg.pair hs))
  have htarget : Primrec (fun p : Input =>
      rawPackedDecode n arity p.1.1.2 (Nat.unpair (Nat.unpair p.2.2.2).2).1) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp (hg.pair hr)
  have hstep : Primrec (fun p : Input => NumberedNumericStep.numericStepTest n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 (Nat.unpair p.2.2.2).1
      (Nat.unpair (Nat.unpair p.2.2.2).2).1 (Nat.unpair (Nat.unpair p.2.2.2).2).2) :=
    (NumberedNumericStepPrimrecProof.numericStepPrimitive n arity).comp
      (hw.pair (ht.pair (hg.pair (hs.pair (hr.pair hcert)))))
  have hbase : Primrec (fun p : (Input × RawPacked n) × RawPacked n => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun p : (Input × RawPacked n) × RawPacked n =>
      ContextUniformPrimary.representative arity p.1.1.1.1.1.1 p.1.1.1.1.1.2 p.1.1.1.1.2 p.1.2) :=
    (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
      ((hw.comp hbase).pair ((hg.comp hbase).pair (Primrec.snd.comp Primrec.fst)))
  have hrr : Primrec (fun p : (Input × RawPacked n) × RawPacked n =>
      ContextUniformPrimary.representative arity p.1.1.1.1.1.1 p.1.1.1.1.1.2 p.1.1.1.1.2 p.2) :=
    (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
      ((hw.comp hbase).pair ((hg.comp hbase).pair Primrec.snd))
  have heq := (Primrec.eq.comp hq (hx.comp hbase)).and (Primrec.eq.comp hrr (hy.comp hbase))
  have hchecked := Primrec.and.comp (hstep.comp hbase) heq.decide
  have hinner := NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive
    (htarget.comp Primrec.fst) hchecked.to₂
  have hprogram := NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive hsource hinner.to₂
  apply hprogram.of_eq
  intro p
  unfold rawEdgeTest
  dsimp only
  cases hs : rawUniverseDecode n arity p.1.1.1.1 p.1.1.1.2 p.1.1.2 (Nat.unpair p.2.2.2).1 with
  | none => rfl
  | some q =>
    cases hr : rawPackedDecode n arity p.1.1.2 (Nat.unpair (Nat.unpair p.2.2.2).2).1 <;>
      simp only [hs,hr,Option.any_none,Option.any_some]

/-- Transfer the implementation proof back to the original checker, on every input. -/
theorem actualJointEdgePrimitive : JointGammaQuotientTargets.ActualJointEdgePrimitive := by
  intro n arity
  exact (rawEdgePrimitive n arity).of_eq (by
    intro p
    exact JointGammaQuotientCalibrationProof.edgeCalibration n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientEdgePrimitiveProof

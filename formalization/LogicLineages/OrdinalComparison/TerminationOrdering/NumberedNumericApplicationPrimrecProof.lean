module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecProof
open Source NumberedRewriteReduction NumberedNumericCarrier NumberedLeastCodeRepresentative
open NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericApplication NumberedNumericApplicationPrimrec
abbrev Input (n : Nat) := (List (Fin n) × List Ty) × Ty × Ty × Nat × Nat
abbrev Inner (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (Input n × Packed (Fin n) arity Gamma) × Packed (Fin n) arity Gamma

theorem applicationProgramCalibration : NumberedNumericApplicationPrimrecTargets.ActualApplicationProgramCalibration :=
  NumberedNumericApplicationPrimrecSupportProof.calibration

theorem programPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Input n => applicationProgram n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hw : Primrec (fun p : Inner n arity Gamma => p.1.1.1) := (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id)))
  have hsigma : Primrec (fun p : Inner n arity Gamma => p.1.1.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
  have htau : Primrec (fun p : Inner n arity Gamma => p.1.1.2.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id)))))
  have hx : Primrec (fun p : Inner n arity Gamma => p.1.1.2.2.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))))
  have hy : Primrec (fun p : Inner n arity Gamma => p.1.1.2.2.2.2) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))))
  have hfcode := (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp
    (g := fun p : Inner n arity Gamma => p.1.2) (Primrec.snd.comp Primrec.fst)
  have hacode := (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp
    (g := fun p : Inner n arity Gamma => p.2) Primrec.snd
  have hft := Primrec.fst.comp hfcode
  have hat := Primrec.fst.comp hacode
  have hfnum := (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
    (g := fun p : Inner n arity Gamma => (p.1.1.1,p.1.2)) (hw.pair (Primrec.snd.comp Primrec.fst))
  have hanum := (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
    (g := fun p : Inner n arity Gamma => (p.1.1.1,p.2)) (hw.pair Primrec.snd)
  have hguard : PrimrecPred (fun p : Inner n arity Gamma =>
      p.1.2.1 = Ty.arrow p.1.1.2.1 p.1.1.2.2.1 ∧ p.2.1 = p.1.1.2.1 ∧
      representativeCode p.1.1.1.1 p.1.1.1.2 p.1.2 = p.1.1.2.2.2.1 ∧
      representativeCode p.1.1.1.1 p.1.1.1.2 p.2 = p.1.1.2.2.2.2) :=
    (Primrec.eq.comp hft (NumberedHeadSignaturePrimrecProof.arrowPrimitive.comp hsigma htau)).and
      ((Primrec.eq.comp hat hsigma).and ((Primrec.eq.comp hfnum hx).and (Primrec.eq.comp hanum hy)))
  have happ := (NumberedCodeAssemblyPrimrecProof.appPrimitive n).comp
    (hsigma.pair ((Primrec.snd.comp hfcode).pair (Primrec.snd.comp hacode)))
  have hdecode := (NumberedPackedStructurePrimrecProof.structuralDecoderPrimitive n arity Gamma).comp (htau.pair happ)
  have hrep : Primrec (fun p : Inner n arity Gamma × Packed (Fin n) arity Gamma =>
      representativeCode p.1.1.1.1.1 p.1.1.1.1.2 p.2) :=
    (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
      (g := fun p : Inner n arity Gamma × Packed (Fin n) arity Gamma => (p.1.1.1.1,p.2))
      ((hw.comp Primrec.fst).pair Primrec.snd)
  have hout := Primrec.option_map hdecode hrep.to₂
  have hinner := Primrec.ite hguard hout (Primrec.const (none : Option Nat))
  have hsecond := (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
    (g := fun p : Input n × Packed (Fin n) arity Gamma => (p.1.1,p.1.2.2.2.2))
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.id)).pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))))
  have hmiddle := Primrec.option_bind hsecond hinner.to₂
  have hfirst := (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
    (g := fun p : Input n => (p.1,p.2.2.2.1))
    (Primrec.fst.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))
  apply (Primrec.option_bind hfirst hmiddle.to₂).of_eq
  intro p
  have mapBind {A B : Type} (o : Option A) (f : A → B) : o.map f = o.bind (fun a => some (f a)) := by
    cases o <;> rfl
  simp only [applicationProgram,packedCode,mapBind]
  rfl

theorem canonicalApplicationPrimitive : NumberedNumericApplicationPrimrecTargets.ActualCanonicalApplicationPrimitive := by
  intro n arity Gamma
  exact (programPrimitive n arity Gamma).of_eq (fun p => applicationProgramCalibration n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecProof

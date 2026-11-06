module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationPrimitiveProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedUniformPackedDecoding
open NumberedNumericCarrier NumberedLeastCodeRepresentative JointGammaApplication

attribute [local irreducible] Primrec

theorem actualRawApplicationCalibration : JointGammaApplicationTargets.ActualRawApplicationCalibration := by
  intro n arity symbols S Gamma sigma tau x y
  rw [← NumberedNumericApplicationPrimrecSupportProof.calibration n arity symbols S Gamma sigma tau x y]
  unfold rawApplication NumberedNumericApplicationPrimrec.applicationProgram
  rw [NumberedUniformPackedDecodingProof.rawUniverseCalibration n arity symbols S Gamma x,
    NumberedUniformPackedDecodingProof.rawUniverseCalibration n arity symbols S Gamma y]
  cases hf : decodeUniverse n arity symbols S Gamma x with
  | none => simp only [Option.map_none,Option.bind_eq_bind,Option.bind_none]
  | some f =>
    cases ha : decodeUniverse n arity symbols S Gamma y with
    | none => simp only [Option.map_some,Option.map_none,Option.bind_eq_bind,Option.bind_some,Option.bind_none]
    | some a =>
      simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some]
      rw [ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma f,
        ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma a]
      simp only [packedCode]
      split_ifs
      · rw [NumberedUniformPackedDecodingProof.rawStructuralCalibration]
        cases hd : decodePacked arity Gamma (tau,Code.app sigma (termCode f.2) (termCode a.2)) with
        | none => rfl
        | some q =>
          simp only [Option.map_some,Option.bind_some,Option.pure_def]
          rw [ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration n arity symbols S Gamma q]
      · rfl

abbrev Inner (n : Nat) := (Input n × RawPacked n) × RawPacked n

theorem rawApplicationPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Input n => rawApplication n arity
      p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hi : Primrec (fun p : Inner n => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : Inner n => p.1.1.1.1) := Primrec.fst.comp (Primrec.fst.comp hi)
  have hg : Primrec (fun p : Inner n => p.1.1.1.2) := Primrec.snd.comp (Primrec.fst.comp hi)
  have hs : Primrec (fun p : Inner n => p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp hi)
  have ht : Primrec (fun p : Inner n => p.1.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hi))
  have hx : Primrec (fun p : Inner n => p.1.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hi)))
  have hy : Primrec (fun p : Inner n => p.1.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hi)))
  have hf : Primrec (fun p : Inner n => p.1.2) := Primrec.snd.comp Primrec.fst
  have ha : Primrec (fun p : Inner n => p.2) := Primrec.snd
  have hfr := (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
    (hw.pair (hg.pair hf))
  have har := (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
    (hw.pair (hg.pair ha))
  have hguard : PrimrecPred (fun p : Inner n =>
      p.1.2.1 = .arrow p.1.1.2.1 p.1.1.2.2.1 ∧ p.2.1 = p.1.1.2.1 ∧
      ContextUniformPrimary.representative arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.1.2 = p.1.1.2.2.2.1 ∧
      ContextUniformPrimary.representative arity p.1.1.1.1.1 p.1.1.1.1.2 p.1.1.1.2 p.2 = p.1.1.2.2.2.2) :=
    (Primrec.eq.comp (Primrec.fst.comp hf) (NumberedHeadSignaturePrimrecProof.arrowPrimitive.comp hs ht)).and
      ((Primrec.eq.comp (Primrec.fst.comp ha) hs).and
        ((Primrec.eq.comp hfr hx).and (Primrec.eq.comp har hy)))
  have happ := (NumberedCodeAssemblyPrimrecProof.appPrimitive n).comp
    (hs.pair ((Primrec.snd.comp hf).pair (Primrec.snd.comp ha)))
  have hd := (NumberedUniformPackedDecodingProof.rawStructuralDecoderPrimitive n arity).comp
    (hg.pair (ht.pair happ))
  have hr : Primrec (fun p : Inner n × RawPacked n =>
      ContextUniformPrimary.representative arity p.1.1.1.1.1.1 p.1.1.1.1.1.2 p.1.1.1.1.2 p.2) :=
    (ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive n arity).comp
      ((hw.comp Primrec.fst).pair ((hg.comp Primrec.fst).pair Primrec.snd))
  have hout := Primrec.option_map hd hr.to₂
  have hinner := Primrec.ite hguard hout (Primrec.const (none : Option Nat))
  have hsecond := (NumberedUniformPackedDecodingProof.rawUniverseDecoderPrimitive n arity).comp
    (g := fun p : Input n × RawPacked n => (p.1.1.1,p.1.1.2,p.1.2.2.2.2))
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
  have hmiddle := Primrec.option_bind hsecond hinner.to₂
  have hfirst := (NumberedUniformPackedDecodingProof.rawUniverseDecoderPrimitive n arity).comp
    (g := fun p : Input n => (p.1.1,p.1.2,p.2.2.2.1))
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  apply (Primrec.option_bind hfirst hmiddle.to₂).of_eq
  intro p
  have mapBind {A B : Type} (o : Option A) (f : A → B) : o.map f = o.bind (fun a => some (f a)) := by
    cases o <;> rfl
  simp only [rawApplication,mapBind]
  rfl

theorem actualOriginalApplicationPrimitive : JointGammaApplicationTargets.ActualOriginalApplicationPrimitive := by
  intro n arity
  exact (rawApplicationPrimitive n arity).of_eq (fun p =>
    actualRawApplicationCalibration n arity p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationPrimitiveProof

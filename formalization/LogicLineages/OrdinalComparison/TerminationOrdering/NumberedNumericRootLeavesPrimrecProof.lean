module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootPrimrecSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootLeavesPrimrecProof
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericCarrier NumberedDirectCertificate NumberedSelectCertificate NumberedNumericRootPrimrec

attribute [local irreducible] Primrec directTarget selectTarget

abbrev Window (n : Nat) := List (Fin n) × List Ty
abbrev BasicInput (n : Nat) := Window n × Nat × Nat
abbrev PutInput (n : Nat) := Window n × Nat × Nat × Nat
abbrev SelectInput (n : Nat) := Window n × List Ty × Nat × Nat × Nat

theorem optionAnyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → Option B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) := by
  apply (Primrec.option_casesOn hf (Primrec.const false) hg).of_eq
  intro a
  cases f a <;> rfl

theorem outputNumberPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Option (Packed (Fin n) arity Gamma) × Nat => outputNumberTest p.1 p.2) := by
  have hnumber : Primrec (fun p : (Option (Packed (Fin n) arity Gamma) × Nat) ×
      Packed (Fin n) arity Gamma => packedNumber p.2) :=
    (NumberedPackedCodecPrimrecProof.packedEncoderPrimitive n arity Gamma).comp
      (g := fun p : (Option (Packed (Fin n) arity Gamma) × Nat) ×
        Packed (Fin n) arity Gamma => p.2) Primrec.snd
  have htest : Primrec (fun p : (Option (Packed (Fin n) arity Gamma) × Nat) ×
      Packed (Fin n) arity Gamma => decide (packedNumber p.2 = p.1.2)) :=
    (Primrec.eq.comp hnumber (Primrec.snd.comp Primrec.fst)).decide
  exact optionAnyPrimitive Primrec.fst htest.to₂

theorem operationNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    {A : Type} [Primcodable A]
    (symbols : A → List (Fin n)) (types : A → List Ty) (source target : A → Nat)
    (operation : A → Packed (Fin n) arity Gamma → Option (Packed (Fin n) arity Gamma))
    (hsymbols : Primrec symbols) (htypes : Primrec types)
    (hsource : Primrec source) (htarget : Primrec target) (hoperation : Primrec₂ operation) :
    Primrec (fun a => (decodeUniverse n arity (symbols a) (types a) Gamma (source a)).any
      (fun q => outputNumberTest (operation a q) (target a))) := by
  have hdecode : Primrec (fun a => decodeUniverse n arity (symbols a) (types a) Gamma (source a)) :=
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      (g := fun a : A => ((symbols a, types a), source a))
      ((hsymbols.pair htypes).pair hsource)
  have hop : Primrec (fun p : A × Packed (Fin n) arity Gamma => operation p.1 p.2) := hoperation
  have hout : Primrec (fun p : A × Packed (Fin n) arity Gamma =>
      outputNumberTest (operation p.1 p.2) (target p.1)) :=
    (outputNumberPrimitive n arity Gamma).comp
      (g := fun p : A × Packed (Fin n) arity Gamma => (operation p.1 p.2, target p.1))
      (hop.pair (htarget.comp Primrec.fst))
  exact optionAnyPrimitive hdecode hout.to₂

theorem putNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : PutInput n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma (.put p.2.1) p.2.2.1 p.2.2.2) := by
  have hop : Primrec (fun p : PutInput n × Packed (Fin n) arity Gamma =>
      directTarget arity Gamma (.put p.1.2.1) p.2) :=
    (NumberedDirectOperationsProof.packedPutPrimitive n arity Gamma).comp
      (g := fun p : PutInput n × Packed (Fin n) arity Gamma => (p.1.2.1, p.2))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact operationNumericPrimitive n arity Gamma
    (fun p : PutInput n => p.1.1) (fun p => p.1.2)
    (fun p => p.2.2.1) (fun p => p.2.2.2)
    (fun p q => directTarget arity Gamma (.put p.2.1) q)
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hop.to₂

theorem fixedDirectNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (rule : DirectRule) (hoperation : Primrec (directTarget arity Gamma rule)) :
    Primrec (fun p : BasicInput n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma rule p.2.1 p.2.2) := by
  have hop : Primrec (fun p : BasicInput n × Packed (Fin n) arity Gamma =>
      directTarget arity Gamma rule p.2) :=
    hoperation.comp (g := fun p : BasicInput n × Packed (Fin n) arity Gamma => p.2) Primrec.snd
  exact operationNumericPrimitive n arity Gamma
    (fun p : BasicInput n => p.1.1) (fun p => p.1.2)
    (fun p => p.2.1) (fun p => p.2.2)
    (fun _ q => directTarget arity Gamma rule q)
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd) hop.to₂

theorem abstractionNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : BasicInput n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma .abstraction p.2.1 p.2.2) :=
  fixedDirectNumericPrimitive n arity Gamma .abstraction
    (NumberedDirectOperationsProof.packedAbstractionPrimitive n arity Gamma)

theorem betaNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : BasicInput n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma .beta p.2.1 p.2.2) :=
  fixedDirectNumericPrimitive n arity Gamma .beta
    (NumberedAuxiliarySubstitutionProof.packedBetaPrimitive n arity Gamma)

theorem bottomNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : BasicInput n =>
      directNumericTest n arity p.1.1 p.1.2 Gamma .bottom p.2.1 p.2.2) :=
  fixedDirectNumericPrimitive n arity Gamma .bottom
    (NumberedDirectOperationsProof.packedBottomPrimitive n arity Gamma)

theorem selectNumericPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : SelectInput n =>
      selectNumericTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hop : Primrec (fun p : SelectInput n × Packed (Fin n) arity Gamma =>
      selectTarget arity Gamma p.1.2.1 p.1.2.2.1 p.2) :=
    (NumberedSelfApplicationProof.packedSelectPrimitive n arity Gamma).comp
      (g := fun p : SelectInput n × Packed (Fin n) arity Gamma => (p.1.2.1, p.1.2.2.1, p.2))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
  exact operationNumericPrimitive n arity Gamma
    (fun p : SelectInput n => p.1.1) (fun p => p.1.2)
    (fun p => p.2.2.2.1) (fun p => p.2.2.2.2)
    (fun p q => selectTarget arity Gamma p.2.1 p.2.2.1 q)
    (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hop.to₂

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootLeavesPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootLeavesPrimrecProof

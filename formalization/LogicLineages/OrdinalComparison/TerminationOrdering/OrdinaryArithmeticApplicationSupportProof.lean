module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationSupportProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticApplication NumberedNumericDecoding NumberedNumericApplication

theorem decodedPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun v : List.Vector Nat 6 => decodedApplication n arity Gamma (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) := by
  have hg (i : Fin 6) : Primrec (fun v : List.Vector Nat 6 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hctx := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp (hg 0)
  have hs : Primrec (fun p : List.Vector Nat 6 × Context n => decodeType (p.1.get 1)) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp ((hg 1).comp Primrec.fst)
  have ht : Primrec (fun p : (List.Vector Nat 6 × Context n) × Ty => decodeType (p.1.1.get 2)) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp ((hg 2).comp (Primrec.fst.comp Primrec.fst))
  have happ : Primrec (fun p : ((List.Vector Nat 6 × Context n) × Ty) × Ty =>
      canonicalApplication n arity p.1.1.2.1.1 p.1.1.2.1.2 Gamma p.1.2 p.2 (p.1.1.1.get 3) (p.1.1.1.get 4)) :=
    (NumberedNumericApplicationPrimrecProof.canonicalApplicationPrimitive n arity Gamma).comp
      (g := fun p : ((List.Vector Nat 6 × Context n) × Ty) × Ty =>
        (p.1.1.2.1,p.1.2,p.2,p.1.1.1.get 3,p.1.1.1.get 4))
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.pair
          (((hg 3).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
           ((hg 4).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))))
  exact Primrec.option_bind hctx (Primrec.option_bind hs (Primrec.option_bind ht happ.to₂).to₂).to₂

theorem valuePrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (applicationValue n arity Gamma) :=
  (Primrec.dom_bool Bool.toNat).comp
    (Primrec.eq.comp (decodedPrimitive n arity Gamma)
      (Primrec.option_some.comp (Primrec.vector_get.comp Primrec.id (Primrec.const (5 : Fin 6))))).decide

theorem valueCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain x y z : Nat) :
    applicationValue n arity Gamma (List.Vector.ofFn ![context,domain,codomain,x,y,z])=1 ↔
      decodedApplication n arity Gamma context domain codomain x y = some z := by
  simp [applicationValue,OrdinaryArithmeticQuotientProof.boolNatOne]

theorem concreteCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty) (x y : Nat) :
    decodedApplication n arity Gamma (contextCode symbols S table)
      (NumberedLeastCodeRepresentative.typeNumber sigma) (NumberedLeastCodeRepresentative.typeNumber tau) x y =
      canonicalApplication n arity symbols S Gamma sigma tau x y := by
  have hs := NumberedNumericDecodingSupportProof.typeRoundTrip sigma
  have ht := NumberedNumericDecodingSupportProof.typeRoundTrip tau
  simp [decodedApplication,contextCode,hs,ht]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationSupportProof

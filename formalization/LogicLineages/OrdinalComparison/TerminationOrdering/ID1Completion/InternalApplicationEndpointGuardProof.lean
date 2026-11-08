module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedStructurePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathPrimrecSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardProof
open Source NumberedRewriteReduction NumberedNumericDecoding NumberedNumericCarrier
open InternalApplicationStepPeel NumberedQuotientPathPrimrecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

/-- A nested option presentation of the unchanged leaf, used only to compose
its existing primitive-recursive decoders. -/
def endpointDispatch (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (v : List.Vector Nat 5) : Nat :=
  ((decodeType (v.get 0)).any (fun sigma =>
    (decodeType (v.get 1)).any (fun tau =>
      (decodeUniverse n arity symbols S Gamma (v.get 2)).any (fun q =>
        (decodePackedNumber n arity Gamma (v.get 3)).any (fun r =>
          (decodeUniverse n arity symbols S Gamma (v.get 4)).any (fun a =>
            decide (q.1 = .arrow sigma tau ∧ r.1 = .arrow sigma tau ∧
              a.1 = sigma ∧ tau ∈ S))))))).toNat

theorem dispatchPrimitive (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) : Primrec (endpointDispatch n arity symbols S Gamma) := by
  let P := Packed (Fin n) arity Gamma
  let A := List.Vector Nat 5
  let B := A × Ty
  let C := B × Ty
  let D := C × P
  let E := D × P
  let F := E × P
  have getP (i : Fin 5) : Primrec (fun v : A => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have dataC : Primrec (fun p : C => p.1.1) := Primrec.fst.comp Primrec.fst
  have dataD : Primrec (fun p : D => p.1.1.1) := dataC.comp Primrec.fst
  have dataE : Primrec (fun p : E => p.1.1.1.1) := dataD.comp Primrec.fst
  have domainDecode : Primrec (fun v : A => decodeType (v.get 0)) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp (getP 0)
  have codomainDecode : Primrec (fun p : B => decodeType (p.1.get 1)) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp ((getP 1).comp Primrec.fst)
  have sourceDecode : Primrec (fun p : C =>
      decodeUniverse n arity symbols S Gamma (p.1.1.get 2)) :=
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      ((Primrec.const (symbols,S)).pair ((getP 2).comp dataC))
  have targetDecode : Primrec (fun p : D =>
      decodePackedNumber n arity Gamma (p.1.1.1.get 3)) :=
    (NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp
      ((getP 3).comp dataD)
  have argumentDecode : Primrec (fun p : E =>
      decodeUniverse n arity symbols S Gamma (p.1.1.1.1.get 4)) :=
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      ((Primrec.const (symbols,S)).pair ((getP 4).comp dataE))
  have sigmaP : Primrec (fun p : F => p.1.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have tauP : Primrec (fun p : F => p.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have qP : Primrec (fun p : F => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have rP : Primrec (fun p : F => p.1.2) := Primrec.snd.comp Primrec.fst
  have aP : Primrec (fun p : F => p.2) := Primrec.snd
  have packedTypeP : Primrec (fun q : P => q.1) :=
    Primrec.fst.comp (NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma)
  have arrowP := NumberedHeadSignaturePrimrecProof.arrowPrimitive.comp sigmaP tauP
  have guardP : PrimrecPred (fun p : F =>
      p.1.1.2.1 = .arrow p.1.1.1.1.2 p.1.1.1.2 ∧
      p.1.2.1 = .arrow p.1.1.1.1.2 p.1.1.1.2 ∧
      p.2.1 = p.1.1.1.1.2 ∧ p.1.1.1.2 ∈ S) :=
    (Primrec.eq.comp (packedTypeP.comp qP) arrowP).and
      ((Primrec.eq.comp (packedTypeP.comp rP) arrowP).and
        ((Primrec.eq.comp (packedTypeP.comp aP) sigmaP).and
          ((NumberedHeadWindowPrimrecProof.memberPrimitive Ty).comp tauP (Primrec.const S))))
  have argumentCase := optionAnyPrimitive argumentDecode guardP.decide.to₂
  have targetCase := optionAnyPrimitive targetDecode argumentCase.to₂
  have sourceCase := optionAnyPrimitive sourceDecode targetCase.to₂
  have codomainCase := optionAnyPrimitive codomainDecode sourceCase.to₂
  have domainCase := optionAnyPrimitive domainDecode codomainCase.to₂
  exact (Primrec.dom_bool Bool.toNat).comp domainCase

theorem dispatchCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (v : List.Vector Nat 5) :
    endpointDispatch n arity symbols S Gamma v = endpointValue n arity symbols S Gamma v := by
  cases hd : decodeType (v.get 0) <;>
    cases ht : decodeType (v.get 1) <;>
    cases hq : decodeUniverse n arity symbols S Gamma (v.get 2) <;>
    cases hr : decodePackedNumber n arity Gamma (v.get 3) <;>
    cases ha : decodeUniverse n arity symbols S Gamma (v.get 4) <;>
    simp only [endpointDispatch, endpointValue, hd, ht, hq, hr, ha,
      Option.any_none, Option.any_some, Bool.toNat_false]

theorem actualOriginalEndpointPrimitive :
    InternalApplicationEndpointGuardTargets.ActualOriginalEndpointPrimitive := by
  intro n arity symbols S Gamma
  exact (dispatchPrimitive n arity symbols S Gamma).of_eq
    (dispatchCalibration n arity symbols S Gamma)

theorem actualOriginalEndpointProgramExists :
    InternalApplicationEndpointGuardTargets.ActualOriginalEndpointProgramExists := by
  intro n arity symbols S Gamma
  exact Proof.allPrimitiveFunctions 5 (endpointValue n arity symbols S Gamma)
    (actualOriginalEndpointPrimitive n arity symbols S Gamma)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationEndpointGuardProof

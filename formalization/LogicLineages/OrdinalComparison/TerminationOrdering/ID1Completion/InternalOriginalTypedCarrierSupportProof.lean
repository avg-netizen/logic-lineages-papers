module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalOriginalTypedCarrier
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

 theorem atValue {n : Nat} (p : Program 1) (i : Fin n) (out : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 p out (xs i)))) :
    Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs)) :=
  unaryValue p (.projection i) out (xs i) xs h (projectionValue i xs)

 theorem atRecover {n : Nat} (p : Program 1) (i : Fin n) (out : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs))) :
    Nonempty (Derivation body Gamma (graph1 p out (xs i))) :=
  unaryRecover p (.projection i) out (xs i) xs h (projectionValue i xs)

 theorem checkerRecover (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2)
    (value typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (accepted validity oldTyped value typ))) :
    Nonempty (Derivation body Gamma (requirements validity oldTyped value typ)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons typ Fin.elim0)
  have hs := conjunctionRecover _ _ xs h
  have ht := conjunctionRecover _ _ xs (andRight hs)
  have htag := InternalStructuralEndpointGuardSupportProof.sameRightRecover
    (leftOf (.projection 0)) (.projection 1) typ xs (andLeft ht) (projectionValue 1 xs)
  exact andIntro (atRecover validity.sourceValid 0 (suc z) xs (andLeft hs))
    (andIntro (atRecover InternalUnpair.left 0 typ xs htag) (andRight ht))

 theorem checkerAccept (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2)
    (value typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (requirements validity oldTyped value typ))) :
    Nonempty (Derivation body Gamma (accepted validity oldTyped value typ)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons typ Fin.elim0)
  have htag := atValue InternalUnpair.left 0 typ xs (andLeft (andRight h))
  exact conjunctionAccept _ _ xs (atValue validity.sourceValid 0 (suc z) xs (andLeft h))
    (conjunctionAccept _ _ xs
      (sameAccept (leftOf (.projection 0)) (.projection 1) typ xs htag (projectionValue 1 xs))
      (andRight (andRight h)))

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof

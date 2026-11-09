module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformVertexPath InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data selectedTyped)
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem ternaryValue {n : Nat} (p : Program 3) (q r s : Program n)
    (out x y w : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph3 p out x y w)))
    (hq : Nonempty (Derivation body Gamma (programGraph q x xs)))
    (hr : Nonempty (Derivation body Gamma (programGraph r y xs)))
    (hs : Nonempty (Derivation body Gamma (programGraph s w xs))) :
    Nonempty (Derivation body Gamma (programGraph (.composition p ![q,r,s]) out xs)) := by
  apply compositionValue p ![q,r,s] out xs (Fin.cons x (Fin.cons y (Fin.cons w Fin.elim0))) hp
  intro i
  exact Fin.cases hq (Fin.cases hr (Fin.cases hs (fun k => Fin.elim0 k))) i

theorem ternaryRecover {n : Nat} (p : Program 3) (q r s : Program n)
    (out x y w : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph (.composition p ![q,r,s]) out xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q x xs)))
    (hr : Nonempty (Derivation body Gamma (programGraph r y xs)))
    (hs : Nonempty (Derivation body Gamma (programGraph s w xs))) :
    Nonempty (Derivation body Gamma (graph3 p out x y w)) := by
  apply compositionRecover p ![q,r,s] out xs (Fin.cons x (Fin.cons y (Fin.cons w Fin.elim0))) hp
  intro i
  exact Fin.cases hq (Fin.cases hr (Fin.cases hs (fun k => Fin.elim0 k))) i

theorem functionTypedRecover (data : Data) (xs : Fin 5 → OTerm α) (arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode arrow (xs 1) (xs 2))))
    (h : Nonempty (Derivation body Gamma (programGraph (functionTyped data) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.typedAccepted data (xs 4) arrow (xs 0))) := by
  have ha := binaryValue InternalListCodec.consCode (.projection 1) (.projection 2)
    arrow (xs 1) (xs 2) xs har (projectionValue 1 xs) (projectionValue 2 xs)
  exact ternaryRecover (selectedTyped data) (.projection 4)
    (consOf (.projection 1) (.projection 2)) (.projection 0) (suc z) (xs 4) arrow (xs 0) xs h
    (projectionValue 4 xs) ha (projectionValue 0 xs)

theorem functionTypedAccept (data : Data) (xs : Fin 5 → OTerm α) (arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode arrow (xs 1) (xs 2))))
    (h : Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.typedAccepted data (xs 4) arrow (xs 0)))) :
    Nonempty (Derivation body Gamma (programGraph (functionTyped data) (suc z) xs)) := by
  have ha := binaryValue InternalListCodec.consCode (.projection 1) (.projection 2)
    arrow (xs 1) (xs 2) xs har (projectionValue 1 xs) (projectionValue 2 xs)
  exact ternaryValue (selectedTyped data) (.projection 4)
    (consOf (.projection 1) (.projection 2)) (.projection 0) (suc z) (xs 4) arrow (xs 0) xs h
    (projectionValue 4 xs) ha (projectionValue 0 xs)

theorem argumentTypedRecover (data : Data) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (argumentTyped data) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.typedAccepted data (xs 3) (xs 1) (xs 0))) :=
  ternaryRecover (selectedTyped data) (.projection 3) (.projection 1) (.projection 0)
    (suc z) (xs 3) (xs 1) (xs 0) xs h
    (projectionValue 3 xs) (projectionValue 1 xs) (projectionValue 0 xs)

theorem argumentTypedAccept (data : Data) (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (InternalParameterizedQuotientEdgeChecker.typedAccepted data (xs 3) (xs 1) (xs 0)))) :
    Nonempty (Derivation body Gamma (programGraph (argumentTyped data) (suc z) xs)) :=
  ternaryValue (selectedTyped data) (.projection 3) (.projection 1) (.projection 0)
    (suc z) (xs 3) (xs 1) (xs 0) xs h
    (projectionValue 3 xs) (projectionValue 1 xs) (projectionValue 0 xs)

theorem activationRecover (data : Data) (p d e a x arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (activationAccepted data p d e a x))) :
    Nonempty (Derivation body Gamma (activationFactors data p d a x arrow)) := by
  let xs := InternalApplicationPathMap.vertexArguments p d e a x
  have hs := conjunctionRecover _ _ xs h
  exact andIntro (functionTypedRecover data xs arrow har (andLeft hs))
    (argumentTypedRecover data xs (andRight hs))

theorem activationAccept (data : Data) (p d e a x arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (activationFactors data p d a x arrow))) :
    Nonempty (Derivation body Gamma (activationAccepted data p d e a x)) := by
  let xs := InternalApplicationPathMap.vertexArguments p d e a x
  exact conjunctionAccept _ _ xs
    (functionTypedAccept data xs arrow har (andLeft h))
    (argumentTypedAccept data xs (andRight h))

theorem activeBranchRecover (data : Data) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (activeBranch data) out xs))) :
    Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.applicationGraph
      data out (xs 1) (xs 2) (xs 4) (xs 3) (xs 0))) := by
  apply compositionRecover (InternalParameterizedCanonicalResultFold.actualJ data)
    ![.projection 1,.projection 2,.projection 4,.projection 3,.projection 0] out xs
    (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 4)
      (Fin.cons (xs 3) (Fin.cons (xs 0) Fin.elim0))))) h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 0 xs) (fun k => Fin.elim0 k))))) i

theorem activeBranchAccept (data : Data) (xs : Fin 5 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.applicationGraph
      data out (xs 1) (xs 2) (xs 4) (xs 3) (xs 0)))) :
    Nonempty (Derivation body Gamma (programGraph (activeBranch data) out xs)) := by
  apply compositionValue (InternalParameterizedCanonicalResultFold.actualJ data)
    ![.projection 1,.projection 2,.projection 4,.projection 3,.projection 0] out xs
    (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 4)
      (Fin.cons (xs 3) (Fin.cons (xs 0) Fin.elim0))))) h
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs)
    (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 0 xs) (fun k => Fin.elim0 k))))) i

theorem vertexRecover (data : Data) (oldVertex : Program 5) (p d e a x out : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activationAccepted data p d e a x)))
    (h : Nonempty (Derivation body Gamma (vertexGraph data oldVertex out p d e a x))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph data out d e x a p)) := by
  let xs := InternalApplicationPathMap.vertexArguments p d e a x
  exact activeBranchRecover data xs out
    (successorBranchElim (activation data) oldVertex (activeBranch data) out z xs ha h)

theorem vertexAccept (data : Data) (oldVertex : Program 5) (p d e a x out : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activationAccepted data p d e a x)))
    (h : Nonempty (Derivation body Gamma
      (InternalParameterizedCanonicalResultFold.applicationGraph data out d e x a p))) :
    Nonempty (Derivation body Gamma (vertexGraph data oldVertex out p d e a x)) := by
  let xs := InternalApplicationPathMap.vertexArguments p d e a x
  exact successorBranchIntro (activation data) oldVertex (activeBranch data) out z xs ha
    (activeBranchAccept data xs out h)

theorem inactiveRecover (data : Data) (oldVertex : Program 5) (p d e a x out : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activationGraph data z p d e a x)))
    (h : Nonempty (Derivation body Gamma (vertexGraph data oldVertex out p d e a x))) :
    Nonempty (Derivation body Gamma (oldVertexGraph oldVertex out p d e a x)) :=
  zeroBranchElim (activation data) oldVertex (activeBranch data) out
    (InternalApplicationPathMap.vertexArguments p d e a x) ha h

theorem inactiveAccept (data : Data) (oldVertex : Program 5) (p d e a x out : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activationGraph data z p d e a x)))
    (h : Nonempty (Derivation body Gamma (oldVertexGraph oldVertex out p d e a x))) :
    Nonempty (Derivation body Gamma (vertexGraph data oldVertex out p d e a x)) :=
  zeroBranchIntro (activation data) oldVertex (activeBranch data) out
    (InternalApplicationPathMap.vertexArguments p d e a x) ha h

theorem invariantRecover (data : Data) (p d e a x arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (invariantAccepted data p d e a x))) :
    Nonempty (Derivation body Gamma (invariantFactors data p d e a x arrow)) := by
  let xs := InternalApplicationPathMap.vertexArguments p d e a x
  have hs := conjunctionRecover _ _ xs h
  exact andIntro (activationRecover data p d e a x arrow har (andLeft hs))
    (binaryRecover data.member (.projection 2) (.projection 0) (suc z) e p xs
      (andRight hs) (projectionValue 2 xs) (projectionValue 0 xs))

theorem invariantAccept (data : Data) (p d e a x arrow : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (h : Nonempty (Derivation body Gamma (invariantFactors data p d e a x arrow))) :
    Nonempty (Derivation body Gamma (invariantAccepted data p d e a x)) := by
  let xs := InternalApplicationPathMap.vertexArguments p d e a x
  exact conjunctionAccept _ _ xs (activationAccept data p d e a x arrow har (andLeft h))
    (binaryValue data.member (.projection 2) (.projection 0) (suc z) e p xs
      (andRight h) (projectionValue 2 xs) (projectionValue 0 xs))

theorem invariantActivation (data : Data) (p d e a x : OTerm α)
    (h : Nonempty (Derivation body Gamma (invariantAccepted data p d e a x))) :
    Nonempty (Derivation body Gamma (activationAccepted data p d e a x)) :=
  andLeft (conjunctionRecover _ _ (InternalApplicationPathMap.vertexArguments p d e a x) h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof

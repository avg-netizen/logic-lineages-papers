module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturn
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
open Source NumberedRewriteSyntax NumberedLeastCodeRepresentative NumberedMultisetNumeric
/-- Standalone return slots, NOT current scheduler jobs. Those jobs omit the
outer type and term/list role; no integration is asserted here. -/
def typ : Program 3 := leftOf (.projection 0)
def payload : Program 3 := rightOf (rightOf (.projection 0))
def tag : Program 3 := leftOf (rightOf (.projection 0))
def domain : Program 3 := leftOf payload
def codomain : Program 3 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => typ)
def tagged (k : Nat) (data : Program 3) : Program 3 := pairOf (constant 3 k) data
def typed (t value : Program 3) := pairOf t value
def sorted (value : Program 3) : Program 3 :=
  .composition OriginalNumericListSort.sort (fun _ : Fin 1 => value)
def headClass (head : Program 3) : Program 3 :=
  .composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => head)
def numberedTail : Program 3 := rightOf (rightOf (rightOf payload))
/-- [original packed root, first completed scalar/list, second completed scalar/list].
Only BASE lists are sorted; extra lists preserve their supplied original order. -/
def returnRoot : Program 3 :=
  OriginalTypedDecoder.ifSame tag (constant 3 0) (tagged 0 (pairOf typ payload))
  (OriginalTypedDecoder.ifSame tag (constant 3 1)
    (tagged 1 (pairOf domain (pairOf codomain (typed codomain (.projection 1)))))
  (OriginalTypedDecoder.ifSame tag (constant 3 2)
    (tagged 2 (pairOf domain (pairOf typ
      (pairOf (typed (consOf domain typ) (.projection 1)) (typed domain (.projection 2))))))
  (OriginalTypedDecoder.ifSame tag (constant 3 3) (tagged 3 typ)
  (OriginalTypedDecoder.ifSame tag (constant 3 4)
    (tagged 4 (pairOf typ (pairOf (headClass (leftOf payload)) (sorted (.projection 1)))))
  (OriginalTypedDecoder.ifSame tag (constant 3 5)
    (tagged 5 (pairOf (leftOf payload) (pairOf typ
      (pairOf (headClass (leftOf (rightOf payload)))
        (pairOf (sorted (.projection 1)) (.projection 2)))))) (constant 3 0))))))
/-- [original raw argument-cons node, completed head scalar, completed tail row]. -/
def returnArgumentsCons : Program 3 :=
  consOf (pairOf (leftOf (rightOf (.projection 0))) (.projection 1)) (.projection 2)
def scalar (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (c : Nat) (q : Packed (Fin n) arity Gamma) : Nat :=
  evaluate Q (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)])
def slots (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (c : Nat) : Packed (Fin n) arity Gamma → Nat × Nat
 | ⟨_,.var _⟩ => (0,0)
 | ⟨_,.bottom _⟩ => (0,0)
 | ⟨_,@AuxTerm.lam _ _ _ d t q⟩ => (scalar Q c ⟨t,q⟩,0)
 | ⟨t,@AuxTerm.app _ _ _ d _ f a⟩ => (scalar Q c ⟨.arrow d t,f⟩,scalar Q c ⟨d,a⟩)
 | ⟨_,.ordinary h base⟩ => (numbersNumber (OriginalRootObservation.argumentValues Q c base),0)
 | ⟨_,.numbered k h _ base _ extras⟩ =>
     (numbersNumber (OriginalRootObservation.argumentValues Q c base),
      numbersNumber (OriginalRootObservation.argumentValues Q c extras))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturn

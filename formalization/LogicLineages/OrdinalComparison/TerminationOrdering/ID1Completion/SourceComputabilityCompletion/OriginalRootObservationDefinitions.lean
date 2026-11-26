module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewDefinitions
public import Mathlib.Data.Multiset.Sort
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric

def packed : Program 2 := .projection 0
def parameter : Program 2 := .projection 1
def resultType : Program 2 := leftOf packed
def raw : Program 2 := rightOf packed
def tag : Program 2 := leftOf raw
def payload : Program 2 := rightOf raw
def domain : Program 2 := leftOf payload
def codomain : Program 2 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => resultType)
def bodyPacked : Program 2 := pairOf codomain (rightOf payload)
def childParameter : Program 2 := pairOf (leftOf parameter) (consOf domain (rightOf parameter))
def typed (R : Program 2) (typ child param : Program 2) : Program 2 :=
 pairOf typ (.composition R ![child,param])
def tagged (k : Nat) (data : Program 2) : Program 2 := pairOf (constant 2 k) data
def variableCase : Program 2 := tagged 0 (pairOf resultType payload)
def bottom : Program 2 := tagged 3 resultType
def lambda (R : Program 2) : Program 2 := tagged 1
 (pairOf domain (pairOf codomain (typed R codomain bodyPacked childParameter)))
def functionPacked : Program 2 := pairOf (consOf domain resultType) (leftOf (rightOf payload))
def argumentPacked : Program 2 := pairOf domain (rightOf (rightOf payload))
def application (R : Program 2) : Program 2 := tagged 2 (pairOf domain (pairOf resultType
 (pairOf (typed R (consOf domain resultType) functionPacked parameter)
   (typed R domain argumentPacked parameter))))
def arguments (R : Program 2) (rawArguments : Program 2) : Program 2 :=
 .composition (OriginalTypedArgumentObservations.argumentObservations R) ![rawArguments,parameter]
def sortedArguments (R : Program 2) (rawArguments : Program 2) : Program 2 :=
 .composition OriginalNumericListSort.sort (fun _ : Fin 1 => arguments R rawArguments)
def headClass (head : Program 2) : Program 2 :=
 .composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => head)
def ordinary (R : Program 2) : Program 2 := tagged 4 (pairOf resultType
 (pairOf (headClass (leftOf payload)) (sortedArguments R (rightOf payload))))
def numberedTail : Program 2 := rightOf (rightOf (rightOf payload))
def numbered (R : Program 2) : Program 2 := tagged 5 (pairOf (leftOf payload)
 (pairOf resultType (pairOf (headClass (leftOf (rightOf payload)))
   (pairOf (sortedArguments R (leftOf numberedTail))
     (arguments R (rightOf (rightOf numberedTail)))))))
/-- Standalone one-level observer. Unknown raw tags, including argument-spine
roots, return zero. It is not a validity checker or a changed source tuple. -/
def rootObservation (R : Program 2) : Program 2 :=
 OriginalTypedDecoder.ifSame tag (constant 2 0) variableCase
 (OriginalTypedDecoder.ifSame tag (constant 2 1) (lambda R)
 (OriginalTypedDecoder.ifSame tag (constant 2 2) (application R)
 (OriginalTypedDecoder.ifSame tag (constant 2 3) bottom
 (OriginalTypedDecoder.ifSame tag (constant 2 4) (ordinary R)
 (OriginalTypedDecoder.ifSame tag (constant 2 5) (numbered R) (constant 2 0))))))

def typedNumber (q : Ty × Nat) : Nat := Nat.pair (typeNumber q.1) q.2
def classNumber {n : Nat} : RecursiveComparison.HeadClass (Fin n) → Nat
 | .native => 0 | .application => 1 | .ranked s => 2+s.val
/-- Canonical numeric multiset encoding retains multiplicity. Only BASE uses
sorting; numbered extra arguments retain their literal order. -/
def multisetNumber (xs : Multiset (Ty × Nat)) : Nat :=
 numbersNumber ((xs.map typedNumber).sort (· ≤ ·))
def signatureNumber {n : Nat} : NumberedHereditaryView.RootSignature n → Nat
 | .var t i => Nat.pair 0 (Nat.pair (typeNumber t) i)
 | .bottom t => Nat.pair 3 (typeNumber t)
 | .lam d t q => Nat.pair 1 (Nat.pair (typeNumber d) (Nat.pair (typeNumber t) (typedNumber q)))
 | .app d t f a => Nat.pair 2 (Nat.pair (typeNumber d) (Nat.pair (typeNumber t) (Nat.pair (typedNumber f) (typedNumber a))))
 | .ordinary t h base => Nat.pair 4 (Nat.pair (typeNumber t) (Nat.pair (classNumber h) (multisetNumber base)))
 | .numbered k t h base extras => Nat.pair 5 (Nat.pair k (Nat.pair (typeNumber t)
   (Nat.pair (classNumber h) (Nat.pair (multisetNumber base) (numbersNumber (extras.map typedNumber))))))

def typedValue (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) (q : Packed (Fin n) arity Gamma) : Nat := Nat.pair (typeNumber q.1)
 (evaluate R (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]))
def argumentValues (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) : List Nat :=
 (argumentList args).map (typedValue R c)
def nativeValue (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) : Packed (Fin n) arity Gamma → Nat
 | ⟨t,.var v⟩ => Nat.pair 0 (Nat.pair (typeNumber t) (SourceTypedPorts.variableIndex v))
 | ⟨t,.bottom _⟩ => Nat.pair 3 (typeNumber t)
 | ⟨_,@AuxTerm.lam _ _ _ d t q⟩ => Nat.pair 1 (Nat.pair (typeNumber d) (Nat.pair (typeNumber t) (typedValue R c ⟨t,q⟩)))
 | ⟨t,@AuxTerm.app _ _ _ d _ f a⟩ => Nat.pair 2 (Nat.pair (typeNumber d) (Nat.pair (typeNumber t)
   (Nat.pair (typedValue R c ⟨.arrow d t,f⟩) (typedValue R c ⟨d,a⟩))))
 | ⟨_,.ordinary h base⟩ => Nat.pair 4 (Nat.pair (typeNumber (headResult h))
   (Nat.pair (classNumber (RecursiveComparison.headClass h)) (numbersNumber ((argumentValues R c base).insertionSort (· ≤ ·)))))
 | ⟨t,.numbered k h _ base _ extras⟩ => Nat.pair 5 (Nat.pair k (Nat.pair (typeNumber t)
   (Nat.pair (classNumber (RecursiveComparison.headClass h))
     (Nat.pair (numbersNumber ((argumentValues R c base).insertionSort (· ≤ ·))) (numbersNumber (argumentValues R c extras))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservation

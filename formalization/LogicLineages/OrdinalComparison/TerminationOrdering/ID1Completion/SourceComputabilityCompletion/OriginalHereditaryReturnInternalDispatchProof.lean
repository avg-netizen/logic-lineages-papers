module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def branch0 : Program 3 := (pairOf (OriginalRawSyntaxTransport.constant 3 0) (pairOf (leftOf (.projection 0)) (rightOf (rightOf (.projection 0)))))
def branch1 : Program 3 := (pairOf (OriginalRawSyntaxTransport.constant 3 1) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (pairOf (.composition InternalListCodec.tailCode (fun _ : Fin 1 => (leftOf (.projection 0)))) (.projection 1)))))
def branch2 : Program 3 := (pairOf (OriginalRawSyntaxTransport.constant 3 2) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (pairOf (consOf (leftOf (rightOf (rightOf (.projection 0)))) (leftOf (.projection 0))) (.projection 1)) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (.projection 2))))))
def branch3 : Program 3 := (pairOf (OriginalRawSyntaxTransport.constant 3 3) (leftOf (.projection 0)))
def branch4 : Program 3 := (pairOf (OriginalRawSyntaxTransport.constant 3 4) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (.projection 0)))))) (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))))))
def branch5 : Program 3 := (pairOf (OriginalRawSyntaxTransport.constant 3 5) (pairOf (leftOf (rightOf (rightOf (.projection 0)))) (pairOf (leftOf (.projection 0)) (pairOf (.composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => (leftOf (rightOf (rightOf (rightOf (.projection 0))))))) (pairOf (.composition OriginalNumericListSort.sort (fun _ : Fin 1 => (.projection 1))) (.projection 2))))))

theorem dispatch0 (input first second out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.tag (numeral 0) input first second)))
 (hv : Nonempty (Derivation body Delta (graph3 branch0 out input first second))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second)) := by
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have h0 := sameYesIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 0) branch0 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))))
   out (numeral 0) (numeral 0) xs ht (constantValue 0 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 0)))) hv
 exact h0

theorem dispatch1 (input first second out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.tag (numeral 1) input first second)))
 (hv : Nonempty (Derivation body Delta (graph3 branch1 out input first second))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second)) := by
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have h1 := sameYesIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))))
   out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1)))) hv
 have h0 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 0) branch0 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))))
   out (numeral 1) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 1 0 (by decide)) h1
 exact h0

theorem dispatch2 (input first second out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.tag (numeral 2) input first second)))
 (hv : Nonempty (Derivation body Delta (graph3 branch2 out input first second))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second)) := by
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have h2 := sameYesIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))
   out (numeral 2) (numeral 2) xs ht (constantValue 2 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 2)))) hv
 have h1 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))))
   out (numeral 2) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 2 1 (by decide)) h2
 have h0 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 0) branch0 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))))
   out (numeral 2) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 2 0 (by decide)) h1
 exact h0

theorem dispatch3 (input first second out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.tag (numeral 3) input first second)))
 (hv : Nonempty (Derivation body Delta (graph3 branch3 out input first second))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second)) := by
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have h3 := sameYesIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))
   out (numeral 3) (numeral 3) xs ht (constantValue 3 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 3)))) hv
 have h2 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))
   out (numeral 3) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 3 2 (by decide)) h3
 have h1 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))))
   out (numeral 3) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 3 1 (by decide)) h2
 have h0 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 0) branch0 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))))
   out (numeral 3) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 3 0 (by decide)) h1
 exact h0

theorem dispatch4 (input first second out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.tag (numeral 4) input first second)))
 (hv : Nonempty (Derivation body Delta (graph3 branch4 out input first second))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second)) := by
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have h4 := sameYesIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))
   out (numeral 4) (numeral 4) xs ht (constantValue 4 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 4)))) hv
 have h3 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))
   out (numeral 4) (numeral 3) xs ht (constantValue 3 xs) (numeralNe 4 3 (by decide)) h4
 have h2 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))
   out (numeral 4) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 4 2 (by decide)) h3
 have h1 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))))
   out (numeral 4) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 4 1 (by decide)) h2
 have h0 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 0) branch0 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))))
   out (numeral 4) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 4 0 (by decide)) h1
 exact h0

theorem dispatch5 (input first second out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.tag (numeral 5) input first second)))
 (hv : Nonempty (Derivation body Delta (graph3 branch5 out input first second))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot out input first second)) := by
 let xs : Fin 3 → OTerm alpha := ![input,first,second]
 have h5 := sameYesIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)
   out (numeral 5) (numeral 5) xs ht (constantValue 5 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 5)))) hv
 have h4 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))
   out (numeral 5) (numeral 4) xs ht (constantValue 4 xs) (numeralNe 5 4 (by decide)) h5
 have h3 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))
   out (numeral 5) (numeral 3) xs ht (constantValue 3 xs) (numeralNe 5 3 (by decide)) h4
 have h2 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))
   out (numeral 5) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 5 2 (by decide)) h3
 have h1 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0)))))
   out (numeral 5) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 5 1 (by decide)) h2
 have h0 := sameNoIntro OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 0) branch0 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 1) branch1 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 2) branch2 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 3) branch3 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 4) branch4 (OriginalTypedDecoder.ifSame OriginalHereditaryReturn.tag (OriginalRawSyntaxTransport.constant 3 5) branch5 (OriginalRawSyntaxTransport.constant 3 0))))))
   out (numeral 5) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 5 0 (by decide)) h1
 exact h0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalDispatchProof

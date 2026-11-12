module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationInheritedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAnnotatedExpansion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def branch1 : Program 4 := termAnnotation (.composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 2))
def branch2 : Program 4 := InternalAcceptance.branch (.projection 0) (termAnnotation (consOf domain (.projection 2))) (termAnnotation domain)
def branch4 : Program 4 := listAnnotation
def branch5 : Program 4 := listAnnotation
def branch7 : Program 4 := InternalAcceptance.branch (.projection 0) (termAnnotation domain) listAnnotation
theorem dispatch1 (index role typ raw out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph4 parentTag (numeral 1) index role typ raw)))
 (hv : Nonempty (Derivation body Delta (graph4 branch1 out index role typ raw))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have h0 := sameYesIntro parentTag (constant 4 1) branch1 (OriginalTypedDecoder.ifSame parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))))
  out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1)))) hv
 exact h0
theorem dispatch2 (index role typ raw out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph4 parentTag (numeral 2) index role typ raw)))
 (hv : Nonempty (Derivation body Delta (graph4 branch2 out index role typ raw))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have h1 := sameYesIntro parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited)))
  out (numeral 2) (numeral 2) xs ht (constantValue 2 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 2)))) hv
 have h0 := sameNoIntro parentTag (constant 4 1) branch1 (OriginalTypedDecoder.ifSame parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))))
  out (numeral 2) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 2 1 (by decide)) h1
 exact h0
theorem dispatch4 (index role typ raw out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph4 parentTag (numeral 4) index role typ raw)))
 (hv : Nonempty (Derivation body Delta (graph4 branch4 out index role typ raw))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have h2 := sameYesIntro parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))
  out (numeral 4) (numeral 4) xs ht (constantValue 4 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 4)))) hv
 have h1 := sameNoIntro parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited)))
  out (numeral 4) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 4 2 (by decide)) h2
 have h0 := sameNoIntro parentTag (constant 4 1) branch1 (OriginalTypedDecoder.ifSame parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))))
  out (numeral 4) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 4 1 (by decide)) h1
 exact h0
theorem dispatch5 (index role typ raw out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph4 parentTag (numeral 5) index role typ raw)))
 (hv : Nonempty (Derivation body Delta (graph4 branch5 out index role typ raw))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have h3 := sameYesIntro parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited)
  out (numeral 5) (numeral 5) xs ht (constantValue 5 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 5)))) hv
 have h2 := sameNoIntro parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))
  out (numeral 5) (numeral 4) xs ht (constantValue 4 xs) (numeralNe 5 4 (by decide)) h3
 have h1 := sameNoIntro parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited)))
  out (numeral 5) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 5 2 (by decide)) h2
 have h0 := sameNoIntro parentTag (constant 4 1) branch1 (OriginalTypedDecoder.ifSame parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))))
  out (numeral 5) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 5 1 (by decide)) h1
 exact h0
theorem dispatch7 (index role typ raw out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph4 parentTag (numeral 7) index role typ raw)))
 (hv : Nonempty (Derivation body Delta (graph4 branch7 out index role typ raw))) :
 Nonempty (Derivation body Delta (graph4 childAnnotation out index role typ raw)) := by
 let xs : Fin 4 → OTerm alpha := ![index,role,typ,raw]
 have h4 := sameYesIntro parentTag (constant 4 7) branch7 inherited
  out (numeral 7) (numeral 7) xs ht (constantValue 7 xs)
  (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 7)))) hv
 have h3 := sameNoIntro parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited)
  out (numeral 7) (numeral 5) xs ht (constantValue 5 xs) (numeralNe 7 5 (by decide)) h4
 have h2 := sameNoIntro parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))
  out (numeral 7) (numeral 4) xs ht (constantValue 4 xs) (numeralNe 7 4 (by decide)) h3
 have h1 := sameNoIntro parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited)))
  out (numeral 7) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 7 2 (by decide)) h2
 have h0 := sameNoIntro parentTag (constant 4 1) branch1 (OriginalTypedDecoder.ifSame parentTag (constant 4 2) branch2 (OriginalTypedDecoder.ifSame parentTag (constant 4 4) branch4 (OriginalTypedDecoder.ifSame parentTag (constant 4 5) branch5 (OriginalTypedDecoder.ifSame parentTag (constant 4 7) branch7 inherited))))
  out (numeral 7) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 7 1 (by decide)) h1
 exact h0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildDispatchProof

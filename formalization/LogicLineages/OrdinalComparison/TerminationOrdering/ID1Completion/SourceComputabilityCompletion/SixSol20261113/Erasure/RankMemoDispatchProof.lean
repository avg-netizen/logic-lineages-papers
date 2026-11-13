module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem dispatch0 (stage tab out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 0) stage tab)))
 (hv : Nonempty (Derivation body Delta (graph2 (constant 2 1) out stage tab))) :
 Nonempty (Derivation body Delta (graph2 nextValue out stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have h0 := sameYesIntro tag (constant 2 0) (constant 2 1) (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))))
   out (numeral 0) (numeral 0) xs ht (constantValue 0 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 0)))) hv
 exact h0

theorem dispatch1 (stage tab out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 1) stage tab)))
 (hv : Nonempty (Derivation body Delta (graph2 (directRank .lambdaBody) out stage tab))) :
 Nonempty (Derivation body Delta (graph2 nextValue out stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have h1 := sameYesIntro tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))))
   out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 1)))) hv
 have h0 := sameNoIntro tag (constant 2 0) (constant 2 1) (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))))
   out (numeral 1) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 1 0 (by decide)) h1
 exact h0

theorem dispatch2 (stage tab out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 2) stage tab)))
 (hv : Nonempty (Derivation body Delta (graph2 (sum (directRank .function) (directRank .argument)) out stage tab))) :
 Nonempty (Derivation body Delta (graph2 nextValue out stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have h2 := sameYesIntro tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))
   out (numeral 2) (numeral 2) xs ht (constantValue 2 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 2)))) hv
 have h1 := sameNoIntro tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))))
   out (numeral 2) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 2 1 (by decide)) h2
 have h0 := sameNoIntro tag (constant 2 0) (constant 2 1) (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))))
   out (numeral 2) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 2 0 (by decide)) h1
 exact h0

theorem dispatch3 (stage tab out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 3) stage tab)))
 (hv : Nonempty (Derivation body Delta (graph2 (constant 2 0) out stage tab))) :
 Nonempty (Derivation body Delta (graph2 nextValue out stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have h3 := sameYesIntro tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))
   out (numeral 3) (numeral 3) xs ht (constantValue 3 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 3)))) hv
 have h2 := sameNoIntro tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))
   out (numeral 3) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 3 2 (by decide)) h3
 have h1 := sameNoIntro tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))))
   out (numeral 3) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 3 1 (by decide)) h2
 have h0 := sameNoIntro tag (constant 2 0) (constant 2 1) (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))))
   out (numeral 3) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 3 0 (by decide)) h1
 exact h0

theorem dispatch4 (stage tab out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 4) stage tab)))
 (hv : Nonempty (Derivation body Delta (graph2 (rowRank .ordinaryBase) out stage tab))) :
 Nonempty (Derivation body Delta (graph2 nextValue out stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have h4 := sameYesIntro tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))
   out (numeral 4) (numeral 4) xs ht (constantValue 4 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 4)))) hv
 have h3 := sameNoIntro tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))
   out (numeral 4) (numeral 3) xs ht (constantValue 3 xs) (numeralNe 4 3 (by decide)) h4
 have h2 := sameNoIntro tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))
   out (numeral 4) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 4 2 (by decide)) h3
 have h1 := sameNoIntro tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))))
   out (numeral 4) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 4 1 (by decide)) h2
 have h0 := sameNoIntro tag (constant 2 0) (constant 2 1) (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))))
   out (numeral 4) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 4 0 (by decide)) h1
 exact h0

theorem dispatch5 (stage tab out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 tag (numeral 5) stage tab)))
 (hv : Nonempty (Derivation body Delta (graph2 (sum (rowRank .numberedBase) (rowRank .numberedExtras)) out stage tab))) :
 Nonempty (Derivation body Delta (graph2 nextValue out stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have h5 := sameYesIntro tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)
   out (numeral 5) (numeral 5) xs ht (constantValue 5 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 5)))) hv
 have h4 := sameNoIntro tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))
   out (numeral 5) (numeral 4) xs ht (constantValue 4 xs) (numeralNe 5 4 (by decide)) h5
 have h3 := sameNoIntro tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))
   out (numeral 5) (numeral 3) xs ht (constantValue 3 xs) (numeralNe 5 3 (by decide)) h4
 have h2 := sameNoIntro tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))
   out (numeral 5) (numeral 2) xs ht (constantValue 2 xs) (numeralNe 5 2 (by decide)) h3
 have h1 := sameNoIntro tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0)))))
   out (numeral 5) (numeral 1) xs ht (constantValue 1 xs) (numeralNe 5 1 (by decide)) h2
 have h0 := sameNoIntro tag (constant 2 0) (constant 2 1) (OriginalTypedDecoder.ifSame tag (constant 2 1) (directRank .lambdaBody) (OriginalTypedDecoder.ifSame tag (constant 2 2) (sum (directRank .function) (directRank .argument)) (OriginalTypedDecoder.ifSame tag (constant 2 3) (constant 2 0) (OriginalTypedDecoder.ifSame tag (constant 2 4) (rowRank .ordinaryBase) (OriginalTypedDecoder.ifSame tag (constant 2 5) (sum (rowRank .numberedBase) (rowRank .numberedExtras)) (constant 2 0))))))
   out (numeral 5) (numeral 0) xs ht (constantValue 0 xs) (numeralNe 5 0 (by decide)) h1
 exact h0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDispatchProof

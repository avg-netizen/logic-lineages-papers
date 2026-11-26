module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.IntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atMapped (n : Nat)
    (labels heads types bases tuples extras out code k encodedHead rawHead t b ts e mappedHeads : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph1 (convertedHeads n) mappedHeads heads)))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![labels,mappedHeads,types,bases,tuples,extras])))
    (hf : Nonempty (Derivation body Delta (Targets.fields n labels heads types bases tuples extras code k encodedHead rawHead t b ts e))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  have h0 := (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))
  have h1 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hf)))))))
  have h2 := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hf))))))
  have h3 := (andRight (andLeft (andLeft (andLeft (andLeft hf)))))
  have h4 := (andRight (andLeft (andLeft (andLeft hf))))
  have h5 := (andRight (andLeft (andLeft hf)))
  have h6 := (andRight (andLeft hf))
  have h7 := (andRight hf)
  have hhead := MapIntroProof.introduce (OriginalEncodedHeadConversion.convert n) heads z mappedHeads rawHead z encodedHead hm h1 h6
  have hfields := andIntro (andIntro (andIntro (andIntro (andIntro h0 hhead) h2) h3) h4) h5
  exact RawMembershipProof.forward labels mappedHeads types bases tuples extras k rawHead t b ts e out code hv h7 hfields

theorem introduction : Targets.InternalIntroduction := by
  intro body alpha Delta n labels heads types bases tuples extras out code k encodedHead rawHead t b ts e hv hf
  apply WrapperCasesProof.cases n labels heads types bases tuples extras out _ hv
  intro beta j Theta mappedHeads hj hm hraw
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [WitnessProof.fieldsRename] at hfj
  exact atMapped n (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
    (tuples.relabel j) (extras.relabel j) (out.relabel j) (code.relabel j) (k.relabel j)
    (encodedHead.relabel j) (rawHead.relabel j) (t.relabel j) (b.relabel j) (ts.relabel j) (e.relabel j)
    mappedHeads hm hraw hfj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.IntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.IntroductionProof

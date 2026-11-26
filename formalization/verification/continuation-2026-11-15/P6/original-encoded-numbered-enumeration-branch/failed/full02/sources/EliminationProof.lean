module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.IntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.RawTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WitnessTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.EliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open WitnessTransportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atConstructor (n : Nat)
    (labels heads types bases tuples extras out code mappedHeads k rawHead t b ts e : OTerm alpha)
    (hmap : Nonempty (Derivation body Delta (graph1 (convertedHeads n) mappedHeads heads)))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![labels,mappedHeads,types,bases,tuples,extras])))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,rawHead,t,b,ts,e]))) :
    Nonempty (Derivation body Delta (InternalFiniteBlocks.block (Targets.witnessMatrix n labels heads types bases tuples extras code))) := by
  have hr := RawMembershipProof.backward labels mappedHeads types bases tuples extras k rawHead t b ts e out code hv hc hm
  have h0 := (andLeft (andLeft (andLeft (andLeft (andLeft hr)))))
  have h1 := (andRight (andLeft (andLeft (andLeft (andLeft hr)))))
  have h2 := (andRight (andLeft (andLeft (andLeft hr))))
  have h3 := (andRight (andLeft (andLeft hr)))
  have h4 := (andRight (andLeft hr))
  have h5 := (andRight hr)
  have hi := MapElimProof.recover (OriginalEncodedHeadConversion.convert n) heads mappedHeads rawHead hmap h1
  apply MapImageEliminationProof.cases (OriginalEncodedHeadConversion.convert n) heads rawHead _ hi
  intro beta j Theta encodedHead hj hhead hconvert
  rw [witnessRename]
  have h0j := InternalGraphCompositionFunctionalityProof.renameInto h0 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at h0j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at h2j
  have h3j := InternalGraphCompositionFunctionalityProof.renameInto h3 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at h3j
  have h4j := InternalGraphCompositionFunctionalityProof.renameInto h4 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at h4j
  have h5j := InternalGraphCompositionFunctionalityProof.renameInto h5 j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at h5j
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [programRename] at hcj
  have hx : (fun i => (![k,rawHead,t,b,ts,e] i).relabel j) = ![k.relabel j,rawHead.relabel j,t.relabel j,b.relabel j,ts.relabel j,e.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hcj
  have hf : Nonempty (Derivation body Theta (Targets.fields n
      (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
      (tuples.relabel j) (extras.relabel j) (code.relabel j) (k.relabel j) encodedHead
      (rawHead.relabel j) (t.relabel j) (b.relabel j) (ts.relabel j) (e.relabel j))) :=
    andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro h0j hhead) h2j) h3j) h4j) h5j) hconvert) hcj
  exact WitnessProof.introduce n (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
    (tuples.relabel j) (extras.relabel j) (code.relabel j) (k.relabel j) encodedHead (rawHead.relabel j)
    (t.relabel j) (b.relabel j) (ts.relabel j) (e.relabel j) hf

theorem atMapped (n : Nat)
    (labels heads types bases tuples extras out code mappedHeads : OTerm alpha)
    (hmap : Nonempty (Derivation body Delta (graph1 (convertedHeads n) mappedHeads heads)))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![labels,mappedHeads,types,bases,tuples,extras])))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (InternalFiniteBlocks.block (Targets.witnessMatrix n labels heads types bases tuples extras code))) := by
  have ht := RawTagProof.tag labels mappedHeads types bases tuples extras out code hv hm
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases code _ ht
  intro beta j Theta k rawHead t b ts e hj hc
  rw [witnessRename]
  have hmapj := InternalGraphCompositionFunctionalityProof.renameInto hmap j Theta hj
  simp only [graph1Rename] at hmapj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [programRename] at hvj
  have hx : (fun i => (![labels,mappedHeads,types,bases,tuples,extras] i).relabel j) =
      ![labels.relabel j,mappedHeads.relabel j,types.relabel j,bases.relabel j,tuples.relabel j,extras.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hvj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact atConstructor n (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
    (tuples.relabel j) (extras.relabel j) (out.relabel j) (code.relabel j) (mappedHeads.relabel j)
    k rawHead t b ts e hmapj hvj hmj hc

theorem elimination : Targets.InternalElimination := by
  intro body alpha Delta n labels heads types bases tuples extras out code hv hm
  apply WrapperCasesProof.cases n labels heads types bases tuples extras out _ hv
  intro beta j Theta mappedHeads hj hmap hraw
  rw [witnessRename]
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact atMapped n (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
    (tuples.relabel j) (extras.relabel j) (out.relabel j) (code.relabel j) mappedHeads hmap hraw hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.EliminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.EliminationProof

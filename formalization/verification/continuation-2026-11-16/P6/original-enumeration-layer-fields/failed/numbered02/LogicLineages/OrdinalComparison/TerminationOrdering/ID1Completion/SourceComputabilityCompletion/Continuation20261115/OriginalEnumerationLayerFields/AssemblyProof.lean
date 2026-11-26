module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapIntroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.AssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalEncodedNumberedEnumerationBranch
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open OriginalEnumerationConstructorLayer.ObservationsProof (componentAt)
open OriginalEnumerationConstructorLayer.MemberProof (merge)
theorem orRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

theorem alternativesRename {beta : Type} (n : Nat) (xs : Fin 7 → OTerm alpha) (code : OTerm alpha) (j : alpha → beta) :
    (Targets.alternatives n xs code).relabel j = Targets.alternatives n (fun i => (xs i).relabel j) (code.relabel j) := by
  simp only [Targets.alternatives,orRename,VariableSyntaxProof.caseRename,LambdaSyntaxProof.caseRename,
    BinarySyntaxProof.caseRename,BottomSyntaxProof.caseRename,OrdinarySyntaxProof.caseRename,
    NumberedSyntaxProof.caseRename,programRename,emptyRename]

theorem forward (n : Nat) (xs : Fin 7 → OTerm alpha) (ys : Fin 8 → OTerm alpha) (code : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (OriginalEnumerationConstructorLayer.Targets.componentGraphs n xs ys)))
    (hm : Nonempty (Derivation body Delta (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :
    Nonempty (Derivation body Delta (Targets.alternatives n xs code)) := by
  let M0 := graph2 contains (numeral 1) (ys 0) code
  obtain ⟨b0⟩ := VariableProof.forward xs (ys 0) code (withHyp (componentAt n xs ys hc 0) M0) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h0 : Nonempty (Derivation body Delta (M0.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orLeft b0)⟩
  let M1 := graph2 contains (numeral 1) (ys 1) code
  obtain ⟨b1⟩ := LambdaProof.forward xs (ys 1) code (withHyp (componentAt n xs ys hc 1) M1) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 : Nonempty (Derivation body Delta (M1.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orLeft b1))⟩
  let M2 := graph2 contains (numeral 1) (ys 2) code
  obtain ⟨b2⟩ := BinaryProof.applicationsForward xs (ys 2) code (withHyp (componentAt n xs ys hc 2) M2) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h2 : Nonempty (Derivation body Delta (M2.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orLeft b2)))⟩
  let M3 := graph2 contains (numeral 1) (ys 3) code
  obtain ⟨b3⟩ := BottomProof.forward xs (ys 3) code (withHyp (componentAt n xs ys hc 3) M3) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h3 : Nonempty (Derivation body Delta (M3.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orLeft b3))))⟩
  let M4 := graph2 contains (numeral 1) (ys 4) code
  obtain ⟨b4⟩ := OrdinaryProof.forward n xs (ys 4) code (withHyp (componentAt n xs ys hc 4) M4) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h4 : Nonempty (Derivation body Delta (M4.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orLeft b4)))))⟩
  let M5 := graph2 contains (numeral 1) (ys 5) code
  obtain ⟨b5⟩ := NumberedProof.forward n xs (ys 5) code (withHyp (componentAt n xs ys hc 5) M5) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h5 : Nonempty (Derivation body Delta (M5.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orRight (orLeft b5))))))⟩
  let M6 := graph2 contains (numeral 1) (ys 6) code
  obtain ⟨b6⟩ := NilProof.forward xs (ys 6) code (withHyp (componentAt n xs ys hc 6) M6) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h6 : Nonempty (Derivation body Delta (M6.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orRight (orRight (orLeft b6)))))))⟩
  let M7 := graph2 contains (numeral 1) (ys 7) code
  obtain ⟨b7⟩ := BinaryProof.argumentConsForward xs (ys 7) code (withHyp (componentAt n xs ys hc 7) M7) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h7 : Nonempty (Derivation body Delta (M7.imp (Targets.alternatives n xs code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orRight (orRight (orRight b7)))))))⟩
  obtain ⟨h⟩ := merge h0 (merge h1 (merge h2 (merge h3 (merge h4 (merge h5 (merge h6 h7))))))
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h hm⟩

theorem backward (n : Nat) (xs : Fin 7 → OTerm alpha) (ys : Fin 8 → OTerm alpha) (code : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (OriginalEnumerationConstructorLayer.Targets.componentGraphs n xs ys)))
    (hm : Nonempty (Derivation body Delta (Targets.alternatives n xs code))) :
    Nonempty (Derivation body Delta (OriginalEnumerationConstructorLayer.Targets.branchMember ys code)) := by
  let M0 := Targets.variableCase (xs 4) code
  obtain ⟨b0⟩ := VariableProof.backward xs (ys 0) code (withHyp (componentAt n xs ys hc 0) M0) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h0 : Nonempty (Derivation body Delta (M0.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orLeft b0)⟩
  let M1 := Targets.lambdaCase (xs 0) (xs 6) code
  obtain ⟨b1⟩ := LambdaProof.backward xs (ys 1) code (withHyp (componentAt n xs ys hc 1) M1) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 : Nonempty (Derivation body Delta (M1.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orLeft b1))⟩
  let M2 := Targets.typedBinaryCase OriginalRawSyntaxTransport.applicationConstructor (xs 0) (xs 5) code
  obtain ⟨b2⟩ := BinaryProof.applicationsBackward xs (ys 2) code (withHyp (componentAt n xs ys hc 2) M2) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h2 : Nonempty (Derivation body Delta (M2.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orLeft b2)))⟩
  let M3 := Targets.bottomCase (xs 0) code
  obtain ⟨b3⟩ := BottomProof.backward xs (ys 3) code (withHyp (componentAt n xs ys hc 3) M3) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h3 : Nonempty (Derivation body Delta (M3.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orLeft b3))))⟩
  let M4 := Targets.ordinaryCase n (xs 1) (xs 5) code
  obtain ⟨b4⟩ := OrdinaryProof.backward n xs (ys 4) code (withHyp (componentAt n xs ys hc 4) M4) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h4 : Nonempty (Derivation body Delta (M4.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orLeft b4)))))⟩
  let M5 := Targets.numberedCase n (xs 2) (xs 1) (xs 0) (xs 3) (xs 5) code
  obtain ⟨b5⟩ := NumberedProof.backward n xs (ys 5) code (withHyp (componentAt n xs ys hc 5) M5) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h5 : Nonempty (Derivation body Delta (M5.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orRight (orLeft b5))))))⟩
  let M6 := programGraph OriginalRawSyntaxTransport.nilConstructor code Fin.elim0
  obtain ⟨b6⟩ := NilProof.backward xs (ys 6) code (withHyp (componentAt n xs ys hc 6) M6) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h6 : Nonempty (Derivation body Delta (M6.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orRight (orRight (orLeft b6)))))))⟩
  let M7 := Targets.typedBinaryCase OriginalRawSyntaxTransport.consConstructor (xs 0) (xs 5) code
  obtain ⟨b7⟩ := BinaryProof.argumentConsBackward xs (ys 7) code (withHyp (componentAt n xs ys hc 7) M7) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h7 : Nonempty (Derivation body Delta (M7.imp (OriginalEnumerationConstructorLayer.Targets.branchMember ys code))) :=
    ⟨Derivation.implicationIntroduction (orRight (orRight (orRight (orRight (orRight (orRight (orRight b7)))))))⟩
  obtain ⟨h⟩ := merge h0 (merge h1 (merge h2 (merge h3 (merge h4 (merge h5 (merge h6 h7))))))
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h hm⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.AssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.AssemblyProof

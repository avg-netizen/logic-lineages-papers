module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.HeadChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LayerCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Lists ListSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem variableCase (n : Nat) (bound raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.variableCase bound raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.VariableSyntaxProof.cases bound raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  exact LeafProof.variableValid n (raw.relabel j) (ys 0) (andRight hf)

theorem bottomCase (n : Nat) (types raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.bottomCase types raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.BottomSyntaxProof.cases types raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  exact LeafProof.bottom n (raw.relabel j) (ys 0) (andRight hf)

theorem lambdaCase (n : Nat) (types opened raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (AllValid n opened)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.lambdaCase types opened raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.LambdaSyntaxProof.cases types opened raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := renameInto hv j Theta hj
  rw [allRename] at hvj
  exact ChildProof.lambda n (raw.relabel j) (ys 0) (ys 1) (andRight hf)
    (ListBindingProof.member n (opened.relabel j) (ys 1) hvj (andRight (andLeft hf)))

theorem applicationCase (n : Nat) (types prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (AllValid n prior)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase applicationConstructor types prior raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.BinarySyntaxProof.cases applicationConstructor types prior raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := renameInto hv j Theta hj
  rw [allRename] at hvj
  exact ChildProof.application n (raw.relabel j) (ys 0) (ys 1) (ys 2) (andRight hf)
    (ListBindingProof.member n (prior.relabel j) (ys 1) hvj (andRight (andLeft (andLeft hf))))
    (ListBindingProof.member n (prior.relabel j) (ys 2) hvj (andRight (andLeft hf)))

theorem consCase (n : Nat) (types prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (AllValid n prior)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.typedBinaryCase consConstructor types prior raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.BinarySyntaxProof.cases consConstructor types prior raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := renameInto hv j Theta hj
  rw [allRename] at hvj
  exact ChildProof.cons n (raw.relabel j) (ys 0) (ys 1) (ys 2) (andRight hf)
    (ListBindingProof.member n (prior.relabel j) (ys 1) hvj (andRight (andLeft (andLeft hf))))
    (ListBindingProof.member n (prior.relabel j) (ys 2) hvj (andRight (andLeft hf)))

theorem ordinaryCase (n : Nat) (heads prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (AllValid n prior)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.ordinaryCase n heads prior raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.OrdinarySyntaxProof.cases n heads prior raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := renameInto hv j Theta hj
  rw [allRename] at hvj
  exact HeadChildProof.ordinary n (raw.relabel j) (ys 1) (ys 2) (andRight hf)
    (OriginalConvertedHeadValidity.Proof.internalConvertedValidity n body beta Theta (ys 0) (ys 1)
      (andRight (andLeft (andLeft hf))))
    (ListBindingProof.member n (prior.relabel j) (ys 2) hvj (andRight (andLeft hf)))

theorem numberedCase (n : Nat) (labels heads types tupleBound prior raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (AllValid n prior)))
    (h : Nonempty (Derivation body Delta (OriginalEnumerationLayerFields.Targets.numberedCase n labels heads types tupleBound prior raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  apply OriginalEnumerationLayerFields.NumberedSyntaxProof.cases n labels heads types tupleBound prior raw _ h
  intro beta j Theta ys hj hf
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hvj := renameInto hv j Theta hj
  rw [allRename] at hvj
  have h9 := andLeft hf
  have h8 := andLeft h9
  have h7 := andLeft h8
  have h6 := andLeft h7
  have h5 := andLeft h6
  have h4 := andLeft h5
  have h3 := andLeft h4
  exact HeadChildProof.numbered n (raw.relabel j) (ys 0) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (andRight hf)
    (OriginalConvertedHeadValidity.Proof.internalConvertedValidity n body beta Theta (ys 1) (ys 2) (andRight h3))
    (ListBindingProof.member n (prior.relabel j) (ys 4) hvj (andRight h5))
    (ListBindingProof.member n (prior.relabel j) (ys 6) hvj (andRight h9))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LayerCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LayerCasesProof

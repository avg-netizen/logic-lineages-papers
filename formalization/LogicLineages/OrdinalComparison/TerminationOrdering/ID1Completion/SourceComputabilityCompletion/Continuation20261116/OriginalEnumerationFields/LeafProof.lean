module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafChooseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem variableAtInput (n : Nat) (xs : Fin 6 → OTerm alpha) (index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor (xs 0) index))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓ InternalLessThan.strictLess index (xs 1)))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    simp only [conjunctionRename,graph1Rename,graph2Rename,sucRelabel,zRelabel,strictRename]
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph1Rename] at hcj
    simp only [programRename,sucRelabel,zRelabel] at hfj
    have hg := AcceptanceProof.validFromFields n (fun i => (xs i).relabel j) hfj
    have hchoose := AcceptanceProof.forward n (fun i => (xs i).relabel j) key param answers hk hp ha hfj
    exact andIntro hg (LeafChooseProof.variableForward n (fun i => (xs i).relabel j) key answers param (index.relabel j) hk hcj hchoose)
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    simp only [programRename,sucRelabel,zRelabel]
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph1Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,sucRelabel,zRelabel,strictRename] at hfj
    have hchoose := LeafChooseProof.variableBackward n (fun i => (xs i).relabel j) key answers param (index.relabel j) hk hcj (andRight hfj)
    exact AcceptanceProof.backward n (fun i => (xs i).relabel j) key param answers hk hp ha (andLeft hfj) hchoose

theorem bottomAtInput (n : Nat) (xs : Fin 6 → OTerm alpha) (typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor (xs 0) typ))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓ graph2 contains (suc z) (xs 2) typ))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    simp only [conjunctionRename,graph1Rename,graph2Rename,sucRelabel,zRelabel,strictRename]
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph1Rename] at hcj
    simp only [programRename,sucRelabel,zRelabel] at hfj
    have hg := AcceptanceProof.validFromFields n (fun i => (xs i).relabel j) hfj
    have hchoose := AcceptanceProof.forward n (fun i => (xs i).relabel j) key param answers hk hp ha hfj
    exact andIntro hg (LeafChooseProof.bottomForward n (fun i => (xs i).relabel j) key answers param (typ.relabel j) hk hp hcj hchoose)
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    simp only [programRename,sucRelabel,zRelabel]
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph1Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,sucRelabel,zRelabel,strictRename] at hfj
    have hchoose := LeafChooseProof.bottomBackward n (fun i => (xs i).relabel j) key answers param (typ.relabel j) hk hp hcj (andRight hfj)
    exact AcceptanceProof.backward n (fun i => (xs i).relabel j) key param answers hk hp ha (andLeft hfj) hchoose

theorem nilAtInput (n : Nat) (xs : Fin 6 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor (xs 0) Fin.elim0))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0)))) := by
  constructor
  · exact AcceptanceProof.validFromFields n xs
  · intro hg
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    simp only [programRename,sucRelabel,zRelabel]
    have hcj := renameInto hc j Theta hj
    have hgj := renameInto hg j Theta hj
    simp only [programRename,InternalControlGraphSupportProof.emptyRename] at hcj
    simp only [graph1Rename,sucRelabel,zRelabel] at hgj
    exact AcceptanceProof.backward n (fun i => (xs i).relabel j) key param answers hk hp ha hgj
      (LeafChooseProof.nilValue n (fun i => (xs i).relabel j) key answers param hk hcj)

theorem internalVariable : Targets.InternalVariable := by
  intro n body alpha Delta raw b S H labels tupleBound index hc
  exact variableAtInput n ![raw,b,S,H,labels,tupleBound] index hc

theorem internalBottom : Targets.InternalBottom := by
  intro n body alpha Delta raw b S H labels tupleBound typ hc
  exact bottomAtInput n ![raw,b,S,H,labels,tupleBound] typ hc

theorem internalNil : Targets.InternalNil := by
  intro n body alpha Delta raw b S H labels tupleBound hc
  exact nilAtInput n ![raw,b,S,H,labels,tupleBound] hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafProof

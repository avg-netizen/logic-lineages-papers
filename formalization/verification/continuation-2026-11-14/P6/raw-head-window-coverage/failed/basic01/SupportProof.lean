module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem consHead {m : Nat} (p q : Program m) (out needle : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p needle xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (consOf p q) out xs))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases q xs _
  intro beta j Theta tail hj hq
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hpj := renameInto hp j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [programRename] at hpj hoj
  have hc := binaryRecover InternalListCodec.consCode p q (out.relabel j) (needle.relabel j) tail
    (fun i => (xs i).relabel j) hoj hpj hq
  exact containsHit (out.relabel j) (needle.relabel j) tail (needle.relabel j) hc ⟨refl _⟩

theorem consTail {m : Nat} (p q : Program m) (out tail needle : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph q tail xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail needle)))
    (ho : Nonempty (Derivation body Delta (programGraph (consOf p q) out xs))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases p xs _
  intro beta j Theta head hj hp
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hqj := renameInto hq j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [programRename] at hqj hoj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hc := binaryRecover InternalListCodec.consCode p q (out.relabel j) head (tail.relabel j)
    (fun i => (xs i).relabel j) hoj hp hqj
  exact PrimaryEdgeInclusion.FilterStepProof.consContainsTail (out.relabel j) head (tail.relabel j) (needle.relabel j) hc hmj

theorem secondHead {m : Nat} (p q r : Program m) (out needle : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hq : Nonempty (Derivation body Delta (programGraph q needle xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (consOf p (consOf q r)) out xs))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases (consOf q r) xs _
  intro beta j Theta tail hj ht
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hqj := renameInto hq j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [programRename] at hqj hoj
  exact consTail p (consOf q r) (out.relabel j) tail (needle.relabel j) (fun i => (xs i).relabel j)
    ht (consHead q r tail (needle.relabel j) _ hqj ht) hoj

theorem appendLeft {m : Nat} (p q : Program m) (out list needle : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph p list xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (programGraph (.composition InternalApplicationValidityStackAppend.append ![p,q]) out xs))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases q xs _
  intro beta j Theta other hj hg
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hkj := renameInto hk j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [programRename] at hkj hoj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have ha := binaryRecover InternalApplicationValidityStackAppend.append p q (out.relabel j)
    (list.relabel j) other (fun i => (xs i).relabel j) hoj hkj hg
  exact PrimaryExpansion.PreservationProof.appendPreservation
    (list.relabel j) other (out.relabel j) (needle.relabel j) ha hmj

theorem appendRight {m : Nat} (p q : Program m) (out list needle : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph q list xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (programGraph (.composition InternalApplicationValidityStackAppend.append ![p,q]) out xs))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases p xs _
  intro beta j Theta other hj hg
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hkj := renameInto hk j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [programRename] at hkj hoj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have ha := binaryRecover InternalApplicationValidityStackAppend.append p q (out.relabel j)
    other (list.relabel j) (fun i => (xs i).relabel j) hoj hg hkj
  exact PrimaryEdgeInclusion.AppendRightProof.appendPreservation
    other (list.relabel j) (out.relabel j) (needle.relabel j) ha hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.SupportProof

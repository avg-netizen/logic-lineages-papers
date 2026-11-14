module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open HeadWindowBranchAdequacy (member)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open ClosureSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem closedApply (types pair left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (ArrowClosed types)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair left right)))
    (hm : Nonempty (Derivation body Delta (member types (suc pair)))) :
    Nonempty (Derivation body Delta (member types left ⊓ member types right)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
    (closureMatrix types) (fun i => InternalTagArithmeticSyntaxProof.emb ((![pair,left,right] : Fin 3 → OTerm alpha) i)) hc
  rw [matrixWitness] at h
  obtain ⟨hh⟩ := andIntro hp hm
  exact ⟨Derivation.implicationElimination h hh⟩

theorem memberTransport (types left right : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn left right)))
    (hm : Nonempty (Derivation body Delta (member types left))) :
    Nonempty (Derivation body Delta (member types right)) := by
  unfold member graph2 programGraph at hm ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
    (OrdinaryArithmetic.graphFormula contains) (numeral 1) ![types,left] ![types,right] _ hm
  intro i
  simp only [InternalSourceInversionSupportProof.onEquality]
  exact Fin.cases (Nonempty.intro (InternalTagArithmeticSupportProof.refl types))
    (Fin.cases he (fun j => Fin.elim0 j)) i

theorem arrowRight (p q : Program 1) (payload out value types : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (ArrowClosed types)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.arrow p q) out payload)))
    (hq : Nonempty (Derivation body Delta (graph1 q value payload)))
    (hm : Nonempty (Derivation body Delta (member types out))) :
    Nonempty (Derivation body Delta (member types value)) := by
  apply programCases p (Fin.cons payload Fin.elim0) _
  intro beta j Theta left hj hp
  simp only [consTermRename,emptyRename] at hp
  have hcj := renameInto hc j Theta hj
  rw [closureRename] at hcj
  have haj := renameInto ha j Theta hj
  have hqj := renameInto hq j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,member,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at haj hqj hmj ⊢
  apply programCases InternalPairing.pairing (Fin.cons left (Fin.cons (value.relabel j) Fin.elim0)) _
  intro gamma k Xi pair hk hpair
  simp only [consTermRename,emptyRename] at hpair
  have hck := renameInto hcj k Xi hk
  rw [closureRename] at hck
  have hak := renameInto haj k Xi hk
  have hqk := renameInto hqj k Xi hk
  have hpk := renameInto hp k Xi hk
  have hmk := renameInto hmj k Xi hk
  simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hak hqk hpk hmk ⊢
  let xs : Fin 1 → OTerm gamma := Fin.cons ((payload.relabel j).relabel k) Fin.elim0
  have hpq : Nonempty (Derivation body Xi (graph1
      (.composition InternalPairing.pairing ![p,q]) pair ((payload.relabel j).relabel k))) :=
    binaryValue InternalPairing.pairing p q pair (left.relabel k) ((value.relabel j).relabel k) xs hpair hpk hqk
  have har : Nonempty (Derivation body Xi (graph1 (OriginalHeadResult.arrow p q) (suc pair) ((payload.relabel j).relabel k))) :=
    unaryValue .succ (.composition InternalPairing.pairing ![p,q]) (suc pair) pair xs
      (successorValue (Fin.cons pair Fin.elim0)) hpq
  have he := valueUnique (OriginalHeadResult.arrow p q) ((out.relabel j).relabel k) (suc pair) xs hak har
  exact andRight (closedApply ((types.relabel j).relabel k) pair (left.relabel k)
    ((value.relabel j).relabel k) hck hpair (memberTransport _ _ _ he hmk))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureProof

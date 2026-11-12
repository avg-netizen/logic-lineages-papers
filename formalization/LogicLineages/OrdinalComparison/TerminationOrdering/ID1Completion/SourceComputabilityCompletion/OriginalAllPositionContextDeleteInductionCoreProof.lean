module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalListCodecSupportProof InternalSourceInversionSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof
open OriginalAllPositionContextDeleteInductionSyntaxProof hiding rowInstantiate rowSuccessor
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Actual length and in-range cutoff force a nonempty original context. -/
theorem contextNonzero (count gamma cutoff : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
    (hb : Nonempty (Derivation body Delta (Below cutoff count))) :
    Nonempty (Derivation body Delta (eqn gamma z).not) := by
  obtain ⟨hl⟩ := hl
  obtain ⟨hb⟩ := hb
  let A := eqn gamma z
  have hz := headTransport length count gamma z Fin.elim0
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (show Nonempty (Derivation body (A :: Delta) (lengthGraph count gamma)) from ⟨addHyp hl A⟩)
  obtain ⟨he⟩ := lengthNilRecover count hz
  have hlt := orderRight cutoff he (addHyp hb A)
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero
    (body := body) (Gamma := A :: Delta) cutoff
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hlt)⟩

theorem zeroAtCons (count gamma head tail deleted d : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields count gamma z deleted d))) :
    Nonempty (Derivation body Delta (Insert d z deleted gamma)) := by
  have hd := andLeft (andRight (andRight hf))
  have hk := andRight (andRight (andRight hf))
  obtain ⟨he⟩ := valueUnique deleteAt deleted tail (Fin.cons z (Fin.cons gamma Fin.elim0)) hd
    (OriginalAllPositionContextDeleteBaseProof.deleteZero gamma head tail hc)
  obtain ⟨heD⟩ := valueUnique InternalRawListRecursion.lookup d head (Fin.cons z (Fin.cons gamma Fin.elim0)) hk
    (OriginalAllPositionContextDeleteBaseProof.lookupZero gamma head tail hc)
  have hc' := binaryInputs InternalListCodec.consCode gamma head tail d deleted ⟨symm heD⟩ ⟨symm he⟩ hc
  exact OriginalContextInsertionZeroProof.zeroBackward d deleted gamma hc'

/-- Bind all real tail witnesses without exposing a metatheoretic choice. -/
theorem tailCases (cutoff head tail : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (count deletedTail deleted : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (lengthGraph count (tail.relabel j))) →
      Nonempty (Derivation body Theta (graph2 deleteAt deletedTail (cutoff.relabel j) (tail.relabel j))) →
      Nonempty (Derivation body Theta (consGraph deleted (head.relabel j) deletedTail)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let l : Program 3 := .composition length (fun _ : Fin 1 => .projection 2)
  let t : Program 3 := .composition deleteAt ![.projection 0,.projection 2]
  let c : Program 3 := .composition InternalListCodec.consCode ![.projection 1,t]
  let qs : Fin 3 → Program 3 := ![l,t,c]
  let xs : Fin 3 → OTerm alpha := ![cutoff,head,tail]
  apply InternalApplicationStepPeelSupportProof.queryCases qs xs psi
  intro beta j ys Theta hj hq
  let xx : Fin 3 → OTerm beta := ![cutoff.relabel j,head.relabel j,tail.relabel j]
  have hxs : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hxs] at hq
  have hl := unaryRecover length (.projection 2) (ys 0) (tail.relabel j) xx (hq 0) (projectionValue 2 xx)
  have ht := binaryRecover deleteAt (.projection 0) (.projection 2) (ys 1) (cutoff.relabel j) (tail.relabel j) xx
    (hq 1) (projectionValue 0 xx) (projectionValue 2 xx)
  have hc := binaryRecover InternalListCodec.consCode (.projection 1) t (ys 2) (head.relabel j) (ys 1) xx
    (hq 2) (projectionValue 1 xx) (hq 1)
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj hl ht hc

theorem successorAtCons (count gamma cutoff head tail deleted d : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields count gamma (suc cutoff) deleted d))) :
    Nonempty (Derivation body Delta (Insert d (suc cutoff) deleted gamma)) := by
  apply tailCases cutoff head tail _
  intro beta j Theta tailCount deletedTail freshDeleted hj hlen hdel hcons
  simp only [insertRename,sucRelabel]
  have hrow' := renameInto hrow j Theta hj
  rw [rowRename] at hrow'
  have hc' := renameInto hc j Theta hj
  rw [consGraphRename] at hc'
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  obtain ⟨heCount⟩ := lengthConsRecover (gamma.relabel j) (head.relabel j) (tail.relabel j)
    (count.relabel j) tailCount hc' (andLeft hf') hlen
  obtain ⟨hlt⟩ := andLeft (andRight hf')
  have hbelow := OriginalContextInsertionBelowCoreProof.successorStrict (cutoff.relabel j) tailCount
    ⟨orderRight (suc (cutoff.relabel j)) heCount hlt⟩
  obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteConsProof.deleteConsIff
    (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) freshDeleted deletedTail hc' hcons
  obtain ⟨hdel⟩ := hdel
  have hparent : Nonempty (Derivation body Theta
      (graph2 deleteAt freshDeleted (suc (cutoff.relabel j)) (gamma.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hiff) hdel⟩
  have heDeleted := valueUnique deleteAt freshDeleted (deleted.relabel j)
    (Fin.cons (suc (cutoff.relabel j)) (Fin.cons (gamma.relabel j) Fin.elim0)) hparent
    (andLeft (andRight (andRight hf')))
  have hconsActual := outputTransport InternalListCodec.consCode freshDeleted (deleted.relabel j)
    (Fin.cons (head.relabel j) (Fin.cons deletedTail Fin.elim0)) heDeleted hcons
  obtain ⟨hlookup⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff
    (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) (d.relabel j) hc'
  obtain ⟨hk⟩ := andRight (andRight (andRight hf'))
  have htailLookup : Nonempty (Derivation body Theta
      (graph2 InternalRawListRecursion.lookup (d.relabel j) (cutoff.relabel j) (tail.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hlookup) hk⟩
  have htailFields := andIntro hlen (andIntro hbelow (andIntro ⟨hdel⟩ htailLookup))
  exact OriginalContextInsertionConsProof.consBackward (d.relabel j) (cutoff.relabel j)
    (deleted.relabel j) (gamma.relabel j) (head.relabel j) deletedTail (tail.relabel j)
    hconsActual hc' (rowApply tailCount (tail.relabel j) (cutoff.relabel j) deletedTail (d.relabel j) hrow' htailFields)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof

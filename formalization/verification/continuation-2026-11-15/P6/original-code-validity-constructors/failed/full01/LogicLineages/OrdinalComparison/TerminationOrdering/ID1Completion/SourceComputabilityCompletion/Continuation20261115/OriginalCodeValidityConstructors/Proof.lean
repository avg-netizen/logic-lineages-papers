module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqnRelabel sucRelabel zRelabel)
open OriginalRawSyntaxTransport
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem disjRename {alpha beta : Type} (a b : Formula alpha) (j : alpha → beta) :
    (a ⊔ b).relabel j = a.relabel j ⊔ b.relabel j := rfl

theorem allowedRename {alpha beta : Type} (n : Nat) (tag payload first second head : OTerm alpha) (j : alpha → beta) :
    (Targets.allowed n tag payload first second head).relabel j =
    Targets.allowed n (tag.relabel j) (payload.relabel j) (first.relabel j) (second.relabel j) (head.relabel j) := by
  simp only [Targets.allowed,disjRename,conjunctionRename,graph1Rename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename]

theorem tableCases (n : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (previous table : OTerm beta), (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 (OriginalCodeDecoderTable.tableProgram n) previous (raw.relabel j) (raw.relabel j))) →
      Nonempty (Derivation body Theta
        (graph2 (OriginalCodeDecoderTable.tableProgram n) table (suc (raw.relabel j)) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let prior : Program 1 := .composition (OriginalCodeDecoderTable.tableProgram n) ![.projection 0,.projection 0]
  let qs : Fin 2 → Program 1 := ![prior,OriginalCodeValidityGuard.table n]
  apply queryCases qs (Fin.cons raw Fin.elim0) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hp := binaryRecover (OriginalCodeDecoderTable.tableProgram n) (.projection 0) (.projection 0)
    (ys 0) (raw.relabel j) (raw.relabel j) xs (hq 0) (projectionValue 0 xs) (projectionValue 0 xs)
  have ht := binaryRecover (OriginalCodeDecoderTable.tableProgram n) (succOf (.projection 0)) (.projection 0)
    (ys 1) (suc (raw.relabel j)) (raw.relabel j) xs (hq 1)
    (OriginalCodeDecoderTable.SupportProof.succProjection 0 xs) (projectionValue 0 xs)
  exact next beta j Theta (ys 0) (ys 1) hj hp ht

theorem guardConstructors : Targets.InternalGuardConstructors := by
  intro n body alpha Delta raw tag payload first second head hp hf hs hh
  constructor
  · intro ha
    apply tableCases n raw _
    intro beta j Theta previous table hj hprior htable
    have hp' := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
    rw [graph2Rename] at hp'
    have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
    rw [graph1Rename] at hf'
    have hs' := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
    rw [graph1Rename] at hs'
    have hh' := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
    rw [graph1Rename] at hh'
    have ha' := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename] at ha'
    rw [allowedRename]
    let f : ClauseProof.Frame n body Theta (raw.relabel j) :=
      { previous := previous, tag := tag.relabel j, payload := payload.relabel j,
        first := first.relabel j, second := second.relabel j, head := head.relabel j,
        prior := hprior, pair := hp', firstGraph := hf', secondGraph := hs', headGraph := hh' }
    exact CoreProof.forward f table htable ha'
  · intro ha
    apply tableCases n raw _
    intro beta j Theta previous table hj hprior htable
    have hp' := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
    rw [graph2Rename] at hp'
    have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
    rw [graph1Rename] at hf'
    have hs' := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
    rw [graph1Rename] at hs'
    have hh' := InternalGraphCompositionFunctionalityProof.renameInto hh j Theta hj
    rw [graph1Rename] at hh'
    have ha' := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
    rw [allowedRename] at ha'
    simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
    let f : ClauseProof.Frame n body Theta (raw.relabel j) :=
      { previous := previous, tag := tag.relabel j, payload := payload.relabel j,
        first := first.relabel j, second := second.relabel j, head := head.relabel j,
        prior := hprior, pair := hp', firstGraph := hf', secondGraph := hs', headGraph := hh' }
    exact CoreProof.backward f table htable ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof

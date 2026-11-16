module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof ChildInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

@[simp] theorem childInputsRename (xs : Fin 6 → OTerm alpha) (child bound : OTerm alpha)
    {beta : Type} (j : alpha → beta) :
    (fun i => (childInputs xs child bound i).relabel j) =
      childInputs (fun i => (xs i).relabel j) (child.relabel j) (bound.relabel j) := by
  funext i
  fin_cases i <;> rfl

theorem atInput (n : Nat) (xs : Fin 6 → OTerm alpha) (typ child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor (xs 0) typ child))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       (graph2 contains (suc z) (xs 2) typ ⊓ programGraph (fields n) (suc z) (childInputs xs child (suc (xs 1))))))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph2Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename] at hfj ⊢
    apply UnaryWitnessProof.cases n (child.relabel j) (suc ((xs 1).relabel j)) param _
    intro gamma k Xi childKey value deps values hxi hck hv hd hl
    have hck' := hck
    rw [sucRelabel] at hck'
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph2Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename] at hff ⊢
    have hchildren := LambdaWitnessProof.forward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((typ.relabel j).relabel k) ((child.relabel j).relabel k)
      childKey value deps values hkk hpk hcc hck' hv hd hl hff
    exact andIntro (AcceptanceProof.validFromFields n (fun i => ((xs i).relabel j).relabel k) hff) hchildren
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph2Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename] at hfj ⊢
    apply UnaryWitnessProof.cases n (child.relabel j) (suc ((xs 1).relabel j)) param _
    intro gamma k Xi childKey value deps values hxi hck hv hd hl
    have hck' := hck
    rw [sucRelabel] at hck'
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph2Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename] at hff ⊢
    exact LambdaWitnessProof.backward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((typ.relabel j).relabel k) ((child.relabel j).relabel k)
      childKey value deps values hkk hpk hcc hck' hv hd hl (andLeft hff) (andLeft (andRight hff)) (andRight (andRight hff))

theorem internalLambda : Targets.InternalLambda := by
  intro n body alpha Delta raw b S H labels tupleBound typ child hc
  exact atInput n ![raw,b,S,H,labels,tupleBound] typ child hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LambdaProof

module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountOpenConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb liftBind varBind zSubst)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans congTerm congSuc)
open ID1Completion.InternalAdditionLawsProof (add addSubst leftZero leftSuccessor)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendListProof (appendZeroRecover consForward)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (nilValue)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCount (entryCount entryStep)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountOpenConsProof (chosenHead otherHead)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev appended (front suffix out : OTerm α) : Formula α := programGraph append out ![front,suffix]

private def congFirst (r : OTerm α) {s t : OTerm α}
    (d : Derivation B Γ (eqn s t)) : Derivation B Γ (eqn (add s r) (add t r)) := by
  have e := congTerm (add (.var (.inr (0 : Fin 1))) (r.relabel Sum.inl)) d
  simpa only [addSubst,varBind,liftBind] using e

private theorem nilCount (key : OTerm α) : Nonempty (Derivation B Γ (counted z key z)) := by
  have h := nilValue (constant 1 0) entryStep (z : OTerm α) ![key]
    (constantZeroValue (body := B) (Gamma := Γ) ![key])
  have xs : (![z,key] : Fin 2 → OTerm α) = Fin.cons z (![key] : Fin 1 → OTerm α) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
  simpa only [counted,xs,recGraph,entryCount] using h

theorem exact_LiteralCountAppendNil (suffix joined key cl cr co : OTerm α)
    (a : Nonempty (Derivation B Γ (appended z suffix joined)))
    (l : Nonempty (Derivation B Γ (counted z key cl)))
    (r : Nonempty (Derivation B Γ (counted suffix key cr)))
    (o : Nonempty (Derivation B Γ (counted joined key co))) :
    Nonempty (Derivation B Γ (eqn co (add cl cr))) := by
  have anchor := appendZeroRecover joined suffix a
  have p : Nonempty (Derivation B Γ (counted suffix key co)) :=
    headTransport entryCount co joined suffix ![key] anchor o
  obtain ⟨hr⟩ := valueUnique entryCount co cr ![suffix,key] p r
  obtain ⟨hl⟩ := valueUnique entryCount cl z ![z,key] l (nilCount key)
  exact ⟨trans hr (trans (symm (leftZero cr)) (congFirst cr (symm hl)))⟩

theorem exact_LiteralCountAppendConsAtReports (front head tail suffix tailOut joined key
    leftTail joinTail cl cr co : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph front head tail)))
    (tailAppend : Nonempty (Derivation B Γ (appended tail suffix tailOut)))
    (wholeAppend : Nonempty (Derivation B Γ (appended front suffix joined)))
    (tl : Nonempty (Derivation B Γ (counted tail key leftTail)))
    (tj : Nonempty (Derivation B Γ (counted tailOut key joinTail)))
    (l : Nonempty (Derivation B Γ (counted front key cl)))
    (o : Nonempty (Derivation B Γ (counted joined key co)))
    (h : Nonempty (Derivation B Γ (eqn joinTail (add leftTail cr)))) :
    Nonempty (Derivation B Γ (eqn co (add cl cr))) := by
  have jCell : Nonempty (Derivation B Γ (consGraph joined head tailOut)) :=
    consForward front head tail suffix tailOut joined cell tailAppend wholeAppend
  let H := eqn head key
  apply formulaCases H
  · have yes : Nonempty (Derivation B (H :: Γ) H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have newL := chosenHead front head tail key leftTail (withHyp cell H) (withHyp tl H) yes
    have newJ := chosenHead joined head tailOut key joinTail (withHyp jCell H) (withHyp tj H) yes
    obtain ⟨el⟩ := valueUnique entryCount cl (suc leftTail) ![front,key] (withHyp l H) newL
    obtain ⟨ej⟩ := valueUnique entryCount co (suc joinTail) ![joined,key] (withHyp o H) newJ
    obtain ⟨eq⟩ := withHyp h H
    exact ⟨trans ej (trans (congSuc eq)
      (trans (symm (leftSuccessor leftTail cr)) (congFirst cr (symm el))))⟩
  · have no : Nonempty (Derivation B (H.not :: Γ) H.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have newL := otherHead front head tail key leftTail (withHyp cell H.not) (withHyp tl H.not) no
    have newJ := otherHead joined head tailOut key joinTail (withHyp jCell H.not) (withHyp tj H.not) no
    obtain ⟨el⟩ := valueUnique entryCount cl leftTail ![front,key] (withHyp l H.not) newL
    obtain ⟨ej⟩ := valueUnique entryCount co joinTail ![joined,key] (withHyp o H.not) newJ
    obtain ⟨eq⟩ := withHyp h H.not
    exact ⟨trans ej (trans eq (congFirst cr (symm el)))⟩

#print axioms exact_LiteralCountAppendNil
#print axioms exact_LiteralCountAppendConsAtReports
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendCoreProof

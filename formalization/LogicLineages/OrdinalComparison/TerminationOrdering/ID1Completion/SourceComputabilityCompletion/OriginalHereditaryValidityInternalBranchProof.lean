module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalNodeSupportProof
open InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The unchanged final constructor dispatch subtree of transition. -/
def dispatch : Program 1 :=
  InternalAcceptance.branch (InternalApplicationStepPeel.same currentTag (two 1))
    (InternalAcceptance.branch
      (InternalApplicationStepPeel.same currentTag (InternalLessThan.constantOne 1))
      popped lambdaExpanded) applicationExpanded

theorem sameRejectAt {n : Nat} (p q : Program n) (x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (hn : Nonempty (Derivation body Delta (equal x y).not)) :
    Nonempty (Derivation body Delta
      (programGraph (InternalApplicationStepPeel.same p q) z xs)) := by
  apply equalityCases x y _
  · intro Theta inc he
    exact binaryValue InternalEqualityTest.equalityTest p q z x y xs he
      (weakenProof hp inc) (weakenProof hq inc)
  · intro Theta inc he
    obtain ⟨hne⟩ := weakenProof hn inc
    obtain ⟨heq⟩ := InternalEqualityTestProof.equalityOfAcceptance x y he
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination hne (by simpa only [equalEqn] using heq))⟩

theorem oneNotTwo : Nonempty (Derivation body Delta
    (equal (numeral 1 : OTerm alpha) (numeral 2)).not) := by
  have h : Derivation body [equal (numeral 1 : OTerm alpha) (numeral 2)]
      (eqn (suc z) (suc (suc z))) := by
    simpa only [equalEqn,numeral] using
      (Derivation.hypothesis List.mem_cons_self : Derivation body
        [equal (numeral 1 : OTerm alpha) (numeral 2)] (equal (numeral 1) (numeral 2)))
  exact ⟨InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.implicationIntroduction (zeroNeSuc (cancelSuc h))) Delta⟩

theorem frameRaw (state workCode frame raw parameter restCode : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode))) :
    Nonempty (Derivation body Delta (graph1 currentRaw raw state)) :=
  andLeft (andRight (andRight (andRight
    (stateFrameOpened state workCode frame raw parameter restCode h))))

theorem frameParameter (state workCode frame raw parameter restCode : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode))) :
    Nonempty (Derivation body Delta (graph1 currentParameter parameter state)) :=
  andLeft (andRight (andRight (andRight (andRight
    (stateFrameOpened state workCode frame raw parameter restCode h)))))

theorem frameRest (state workCode frame raw parameter restCode : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode))) :
    Nonempty (Derivation body Delta (graph1 rest restCode state)) :=
  andRight (andRight (andRight (andRight (andRight
    (stateFrameOpened state workCode frame raw parameter restCode h)))))

theorem frameTag (state workCode frame raw parameter restCode tag : OTerm alpha)
    (h : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw))) :
    Nonempty (Derivation body Delta (graph1 currentTag tag state)) :=
  unaryValue OriginalLambdaConstructor.tag currentRaw tag raw (Fin.cons state Fin.elim0)
    ht (frameRaw state workCode frame raw parameter restCode h)

/-- Discharge the actual status, nonempty-work and accepted-node envelope. -/
theorem acceptingVisitIntro (s t m : Program 2)
    (state workCode frame raw parameter restCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (hd : Nonempty (Derivation body Delta (graph1 dispatch out state))) :
    Nonempty (Derivation body Delta (graph1 (transition s t m) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hw := pairRight state (numeral 1) workCode (andLeft hs)
  have hc := InternalListCodecSupportProof.consDestruction workCode frame restCode (andLeft (andRight hs))
  apply successorBranchIntro _ _ _ out z xs
    (exactAccept status xs (pairLeft state (numeral 1) workCode (andLeft hs)))
  apply nonzeroBranchIntro _ _ _ out workCode xs hw (andRight (andRight hc))
  exact successorBranchIntro _ _ _ out z xs (exactAccept (nodeCheck s t m) xs hn) hd

theorem acceptingVisitElim (s t m : Program 2)
    (state workCode frame raw parameter restCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (graph1 dispatch out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hw := pairRight state (numeral 1) workCode (andLeft hs)
  have hc := InternalListCodecSupportProof.consDestruction workCode frame restCode (andLeft (andRight hs))
  have hstatus := exactAccept status xs (pairLeft state (numeral 1) workCode (andLeft hs))
  have hlive := successorBranchElim _ _ _ out z xs hstatus ho
  have hchecked := nonzeroBranchElim _ _ _ out workCode xs hw (andRight (andRight hc)) hlive
  exact successorBranchElim _ _ _ out z xs (exactAccept (nodeCheck s t m) xs hn) hchecked

theorem applicationIntro (state out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 currentTag (numeral 2) state)))
    (ho : Nonempty (Derivation body Delta (graph1 applicationExpanded out state))) :
    Nonempty (Derivation body Delta (graph1 dispatch out state)) :=
  successorBranchIntro _ _ _ out z (Fin.cons state Fin.elim0)
    (InternalApplicationStepPeelSupportProof.sameAccept currentTag (two 1) (numeral 2)
      (Fin.cons state Fin.elim0) ht (twoValue _)) ho

theorem applicationElim (state out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 currentTag (numeral 2) state)))
    (ho : Nonempty (Derivation body Delta (graph1 dispatch out state))) :
    Nonempty (Derivation body Delta (graph1 applicationExpanded out state)) :=
  successorBranchElim _ _ _ out z (Fin.cons state Fin.elim0)
    (InternalApplicationStepPeelSupportProof.sameAccept currentTag (two 1) (numeral 2)
      (Fin.cons state Fin.elim0) ht (twoValue _)) ho

theorem lambdaIntro (state out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 currentTag (numeral 1) state)))
    (ho : Nonempty (Derivation body Delta (graph1 lambdaExpanded out state))) :
    Nonempty (Derivation body Delta (graph1 dispatch out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply zeroBranchIntro _ _ _ out xs
    (sameRejectAt currentTag (two 1) (numeral 1) (numeral 2) xs ht (twoValue xs) oneNotTwo)
  exact successorBranchIntro _ _ _ out z xs
    (InternalApplicationStepPeelSupportProof.sameAccept currentTag (InternalLessThan.constantOne 1)
      (numeral 1) xs ht (InternalLessThanSupportProof.oneConstantValue xs)) ho

theorem lambdaElim (state out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 currentTag (numeral 1) state)))
    (ho : Nonempty (Derivation body Delta (graph1 dispatch out state))) :
    Nonempty (Derivation body Delta (graph1 lambdaExpanded out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hz := zeroBranchElim _ _ _ out xs
    (sameRejectAt currentTag (two 1) (numeral 1) (numeral 2) xs ht (twoValue xs) oneNotTwo) ho
  exact successorBranchElim _ _ _ out z xs
    (InternalApplicationStepPeelSupportProof.sameAccept currentTag (InternalLessThan.constantOne 1)
      (numeral 1) xs ht (InternalLessThanSupportProof.oneConstantValue xs)) hz

theorem popIntro (state tag out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 currentTag tag state)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Delta (equal tag (numeral 1)).not))
    (ho : Nonempty (Derivation body Delta (graph1 popped out state))) :
    Nonempty (Derivation body Delta (graph1 dispatch out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply zeroBranchIntro _ _ _ out xs
    (sameRejectAt currentTag (two 1) tag (numeral 2) xs ht (twoValue xs) h2)
  exact zeroBranchIntro _ _ _ out xs
    (sameRejectAt currentTag (InternalLessThan.constantOne 1) tag (numeral 1) xs ht
      (InternalLessThanSupportProof.oneConstantValue xs) h1) ho

theorem popElim (state tag out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 currentTag tag state)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Delta (equal tag (numeral 1)).not))
    (ho : Nonempty (Derivation body Delta (graph1 dispatch out state))) :
    Nonempty (Derivation body Delta (graph1 popped out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hz := zeroBranchElim _ _ _ out xs
    (sameRejectAt currentTag (two 1) tag (numeral 2) xs ht (twoValue xs) h2) ho
  exact zeroBranchElim _ _ _ out xs
    (sameRejectAt currentTag (InternalLessThan.constantOne 1) tag (numeral 1) xs ht
      (InternalLessThanSupportProof.oneConstantValue xs) h1) hz

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof

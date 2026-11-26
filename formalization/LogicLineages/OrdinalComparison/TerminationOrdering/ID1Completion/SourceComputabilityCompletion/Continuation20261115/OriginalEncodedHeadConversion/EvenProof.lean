module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SplitBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.EvenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof
open SplitInductionDefinitions SplitInductionSyntaxProof SplitBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem baseValue (out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z z))) :
    Nonempty (Derivation body Delta (graph1 split out (double z))) := by
  have he := valueUnique InternalPairing.pairing z out ![z,z]
    InternalApplicationValidityStackAppendTransitionProof.pairZero hp
  have hs := outputTransport split z out ![z] he StepProof.splitZero
  exact headTransport split out z (double z) Fin.elim0 ⟨symm (addZero z)⟩ hs

theorem atStates (raw out old middle : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (AtRaw raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc raw) z)))
    (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing old raw z)))
    (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing middle raw (suc z)))) :
    Nonempty (Derivation body Delta (graph1 split out (double (suc raw)))) := by
  have hi := atRawApply raw old ih h0
  have hm := StepProof.splitSuccessor (double raw) old middle hi
    (StepProof.advanceZero (double raw) old middle raw h0 h1)
  have ho := StepProof.splitSuccessor (suc (double raw)) middle out hm
    (StepProof.advanceOne (suc (double raw)) middle out raw h1 hp)
  have he : Derivation body Delta (eqn (double (suc raw)) (suc (suc (double raw)))) :=
    trans (InternalAdditionLawsProof.leftSuccessor raw (suc raw)) (congSuc (addSucc raw raw))
  exact headTransport split out (suc (suc (double raw))) (double (suc raw)) Fin.elim0 ⟨symm he⟩ ho

theorem successorValue (raw out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (AtRaw raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc raw) z))) :
    Nonempty (Derivation body Delta (graph1 split out (double (suc raw)))) := by
  let qs : Fin 2 → Program 1 := ![pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 0),
    pairOf (.projection 0) (OriginalRawSyntaxTransport.constant 1 1)]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename,double,InternalOriginalOrderSyntaxProof.addRelabel,sucRelabel]
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  rw [atRawRename] at ihj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  simp only [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename,sucRelabel,zRelabel] at hpj
  have hq0 := hq 0
  have hq1 := hq 1
  simp only [consTermRename,InternalControlGraphSupportProof.emptyRename] at hq0 hq1
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have h0 := binaryRecover InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 1 0)
    (ys 0) (raw.relabel j) z xs hq0 (projectionValue 0 xs) (constantValue 0 xs)
  have h1 := binaryRecover InternalPairing.pairing (.projection 0) (OriginalRawSyntaxTransport.constant 1 1)
    (ys 1) (raw.relabel j) (suc z) xs hq1 (projectionValue 0 xs) (constantValue 1 xs)
  exact atStates (raw.relabel j) (out.relabel j) (ys 0) (ys 1) ihj hpj h0 h1

theorem basePredicate : Nonempty (Derivation body Delta (AtRaw z)) := by
  apply atRawIntro z
  simp only [matrix,fields,result,zRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  exact Classical.choice (baseValue (.var (.inr 0) : OTerm (alpha ⊕ Fin 1)) ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem stepPredicate (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (AtRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw (suc raw))) := by
  apply atRawIntro (suc raw)
  simp only [matrix,fields,result,sucRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let x := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)
  let out : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let Theta := graph2 InternalPairing.pairing out (suc x) z :: Delta.map (fun q => q.relabel Sum.inl)
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hj
  rw [atRawRename] at ihj
  exact Classical.choice (successorValue x out ihj ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem evenGraph (raw out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out raw z))) :
    Nonempty (Derivation body Delta (graph1 split out (double raw))) :=
  atRawApply raw out (SplitBindingProof.induction raw basePredicate (fun _ _ x h => stepPredicate x h)) hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.EvenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.EvenProof

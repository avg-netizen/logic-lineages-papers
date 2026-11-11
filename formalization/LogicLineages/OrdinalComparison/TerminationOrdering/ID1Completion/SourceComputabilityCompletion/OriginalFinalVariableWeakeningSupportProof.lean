module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalRawSyntaxTransportInternalVariableSupportProof (variableConstructorPair)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe numeralNeApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Compose using actual intermediate graph values in BOTH directions. -/
theorem compositionEquation {m n : Nat} (f : Program n) (g : Fin n → Program m)
    (out : OTerm alpha) (xs : Fin m → OTerm alpha) (ys : Fin n → OTerm alpha)
    (hg : ∀ i, Nonempty (Derivation body Gamma (programGraph (g i) (ys i) xs))) :
    Nonempty (Derivation body Gamma
      ((programGraph (.composition f g) out xs).iff (programGraph f out ys))) := by
  let A := programGraph (.composition f g) out xs
  let B := programGraph f out ys
  obtain ⟨hf⟩ := compositionRecover f g out xs ys
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩) (fun i => addAssumption (hg i) A)
  obtain ⟨hb⟩ := compositionValue f g out xs ys
    (show Nonempty (Derivation body (B :: Gamma) B) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩) (fun i => addAssumption (hg i) B)
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

/-- The packed variable has the original literal tag zero. -/
theorem packedVariableTag (raw variableCode typ index : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode))) :
    Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag z raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have hc := variableConstructorPair variableCode index hv
  have hr := unaryValue InternalUnpair.right (.projection 0) variableCode raw xs
    (pairRight raw typ variableCode hp) (projectionValue 0 xs)
  exact unaryValue InternalUnpair.left (rightOf (.projection 0)) z variableCode xs
    (pairLeft variableCode z index hc) hr

/-- The original variable-test control is paid at the unchanged raw value. -/
theorem variableControl (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag z raw))) :
    Nonempty (Derivation body Gamma
      (graph2 OriginalVariableLeaves.variableTag (numeral 1) raw parameter)) := by
  have htest : Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest (numeral 1) raw)) :=
    sameAccept OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1) z
      (Fin.cons raw Fin.elim0) ht (InternalLessThanSupportProof.zeroConstantValue _)
  exact unaryValue OriginalConstructorLeaf.variableTest (.projection 0) (numeral 1) raw
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) htest
    (projectionValue 0 (Fin.cons raw (Fin.cons parameter Fin.elim0)))

/-- Zero differs internally from both structural tags, so the actual original
OTHER AST accepts. No native classification or desired acceptance is assumed. -/
theorem variableOther (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag z raw))) :
    Nonempty (Derivation body Gamma
      (graph1 OriginalLambdaTraversalInternal.otherTag (numeral 1) raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have h2 := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    OriginalLambdaTraversal.rawTag (two 1) z (numeral 2) xs ht (twoValue xs)
    (numeralNe 0 2 (by decide))
  have h1 := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    OriginalLambdaTraversal.rawTag (InternalLessThan.constantOne 1) z (numeral 1) xs ht
    (InternalLessThanSupportProof.oneConstantValue xs) (numeralNe 0 1 (by decide))
  exact zeroBranchIntro _ _ _ (numeral 1) xs h2
    (zeroBranchIntro _ _ _ (numeral 1) xs h1 (InternalLessThanSupportProof.oneConstantValue xs))

/-- Exact bottom acceptance forces tag three, contrary to the actual zero tag. -/
theorem variableNotBottom (raw : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag z raw))) :
    Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw).not) := by
  let B := BottomRepresentative.bottomGraph (numeral 1) raw
  have hb : Nonempty (Derivation body (B :: Gamma) B) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h3 := OriginalTransparentLambdaValidityInternalBottomShapeProof.bottomTag raw hb
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag z (numeral 3)
    (Fin.cons raw Fin.elim0) (addAssumption ht B) h3
  exact ⟨Derivation.implicationIntroduction (numeralNeApply 0 3 (by decide) he)⟩

/-- Actual selectors expose the original dependent-decoder coordinates. -/
theorem variableCoordinates (raw variableCode typ index parameter context gamma : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    ∀ i : Fin 3, Nonempty (Derivation body Gamma
      (programGraph ((![leftOf (.projection 0),rightOf (rightOf (.projection 0)),
        rightOf (.projection 1)] : Fin 3 → Program 2) i)
        (![typ,index,gamma] i) (Fin.cons raw (Fin.cons parameter Fin.elim0)))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hc := variableConstructorPair variableCode index hv
  have hraw := unaryValue InternalUnpair.right (.projection 0) variableCode raw xs
    (pairRight raw typ variableCode hr) (projectionValue 0 xs)
  have htyp := unaryValue InternalUnpair.left (.projection 0) typ raw xs
    (pairLeft raw typ variableCode hr) (projectionValue 0 xs)
  have hi := unaryValue InternalUnpair.right (rightOf (.projection 0)) index variableCode xs
    (pairRight variableCode z index hc) hraw
  have hg := unaryValue InternalUnpair.right (.projection 1) gamma parameter xs
    (pairRight parameter context gamma hp) (projectionValue 1 xs)
  intro i
  exact Fin.cases htyp (Fin.cases hi (Fin.cases hg (fun j => Fin.elim0 j))) i

theorem variableCheckEquation (out raw variableCode typ index parameter context gamma : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 OriginalVariableLeaves.variableCheck out raw parameter).iff
        (OriginalVariableDecoder.graph out typ index gamma))) :=
  compositionEquation OriginalVariableDecoder.check
    ![leftOf (.projection 0),rightOf (rightOf (.projection 0)),rightOf (.projection 1)] out
    (Fin.cons raw (Fin.cons parameter Fin.elim0))
    (Fin.cons typ (Fin.cons index (Fin.cons gamma Fin.elim0)))
    (variableCoordinates raw variableCode typ index parameter context gamma hv hr hp)

/-- The target's outer-context guard stays on literally the SAME Context. -/
theorem contextCheckEquation (guard : Program 1)
    (out raw parameter context gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalVariableLeaves.contextCheck guard) out raw parameter).iff
        (graph1 guard out context))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply compositionEquation guard (fun _ : Fin 1 => leftOf (.projection 1)) out xs
    (Fin.cons context Fin.elim0)
  intro i
  obtain rfl := Fin.eq_zero i
  exact unaryValue InternalUnpair.left (.projection 1) context parameter xs
    (pairLeft parameter context gamma hp) (projectionValue 1 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof

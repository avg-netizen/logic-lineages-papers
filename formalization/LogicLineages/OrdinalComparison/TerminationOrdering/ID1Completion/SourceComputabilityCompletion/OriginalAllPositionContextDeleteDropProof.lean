module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalRawListRecursion InternalRawListRecursionSyntaxProof InternalRawListRecursionSupportProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (OTerm z suc emb zRelabel sucRelabel varBind nextTerm)
open InternalTagArithmeticSupportProof InternalTermSubstitutionProof
open InternalListCodecSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight queryCases)
open OriginalAllPositionContextDeleteDropSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (gamma head tail out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 drop out z tail))) :
    Nonempty (Derivation body Delta (graph2 drop out (suc z) gamma)) := by
  have he := valueUnique drop tail out (Fin.cons z (Fin.cons tail Fin.elim0)) (dropZero tail) hd
  exact outputTransport drop tail out (Fin.cons (suc z) (Fin.cons gamma Fin.elim0)) he
    (dropNext tail gamma z gamma (dropZero gamma) (andLeft (andRight (consDestruction gamma head tail hc))))

theorem succCore (count gamma head tail out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 drop out (suc count) tail))) :
    Nonempty (Derivation body Delta (graph2 drop out (suc (suc count)) gamma)) := by
  let next : Program 2 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => drop)
  let qs : Fin 2 → Program 2 := ![drop,next]
  let xs : Fin 2 → OTerm alpha := Fin.cons count (Fin.cons tail Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [graph2Rename,sucRelabel]
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hc' := renameInto hc j Theta hj
  have hd' := renameInto hd j Theta hj
  simp only [graph2Rename,sucRelabel] at hc' hd'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (count.relabel j) (Fin.cons (tail.relabel j) Fin.elim0)
  have ht := unaryRecover InternalListCodec.tailCode drop (ys 1) (ys 0) xx (hq 1) (hq 0)
  have prev := rowApply (count.relabel j) (gamma.relabel j) (head.relabel j) (tail.relabel j) (ys 0) hr' hc' (hq 0)
  have left := dropNext (ys 1) (ys 0) (suc (count.relabel j)) (gamma.relabel j) prev ht
  have right := dropNext (ys 1) (ys 0) (count.relabel j) (tail.relabel j) (hq 0) ht
  have he := valueUnique drop (ys 1) (out.relabel j)
    (Fin.cons (suc (count.relabel j)) (Fin.cons (tail.relabel j) Fin.elim0)) right hd'
  exact outputTransport drop (ys 1) (out.relabel j)
    (Fin.cons (suc (suc (count.relabel j))) (Fin.cons (gamma.relabel j) Fin.elim0)) he left

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let gamma : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let head : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let tail : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c : OTerm (alpha ⊕ Fin 4) := z
  let A := graph2 InternalListCodec.consCode gamma head tail ⊓ graph2 drop out z tail
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl)) gamma head tail out
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [rowBody,zRelabel,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (count : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count))) : Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let gamma : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let head : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let tail : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c : OTerm (alpha ⊕ Fin 4) := count.relabel Sum.inl
  let A := graph2 InternalListCodec.consCode gamma head tail ⊓ graph2 drop out (suc c) tail
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hr' := renameInto hr Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hr'
  obtain ⟨h⟩ := succCore c gamma head tail out hr'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [rowBody,zRelabel,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem dropConsBackward (gamma head tail cutoff out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 drop out cutoff tail))) :
    Nonempty (Derivation body Delta (graph2 drop out (suc cutoff) gamma)) :=
  rowApply cutoff gamma head tail out (allRows cutoff) hc hd

theorem dropConsForward (gamma head tail cutoff out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 drop out (suc cutoff) gamma))) :
    Nonempty (Derivation body Delta (graph2 drop out cutoff tail)) := by
  apply programCases drop (Fin.cons cutoff (Fin.cons tail Fin.elim0)) _
  intro beta j Theta actual hj ha
  rw [graph2Rename]
  have hc' := renameInto hc j Theta hj
  have hd' := renameInto hd j Theta hj
  simp only [graph2Rename,sucRelabel] at hc' hd'
  simp only [consTermRename,emptyRename] at ha
  have hleft := dropConsBackward (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) actual hc' ha
  have he := valueUnique drop actual (out.relabel j)
    (Fin.cons (suc (cutoff.relabel j)) (Fin.cons (gamma.relabel j) Fin.elim0)) hleft hd'
  exact outputTransport drop actual (out.relabel j)
    (Fin.cons (cutoff.relabel j) (Fin.cons (tail.relabel j) Fin.elim0)) he ha

theorem dropConsIff (gamma head tail cutoff out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail))) :
    Nonempty (Derivation body Delta
      ((graph2 drop out (suc cutoff) gamma).iff (graph2 drop out cutoff tail))) := by
  let A := graph2 drop out (suc cutoff) gamma
  let B := graph2 drop out cutoff tail
  obtain ⟨hf⟩ := dropConsForward gamma head tail cutoff out (withHyp hc A)
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := dropConsBackward gamma head tail cutoff out (withHyp hc B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem lookupConsIff (gamma head tail cutoff out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode gamma head tail))) :
    Nonempty (Derivation body Delta
      ((graph2 lookup out (suc cutoff) gamma).iff (graph2 lookup out cutoff tail))) := by
  apply programCases drop (Fin.cons cutoff (Fin.cons tail Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [OriginalTypedDecoderTransportLogicalProof.iffRename,graph2Rename,sucRelabel]
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  simp only [consTermRename,emptyRename] at hr
  have hl := dropConsBackward (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) rest hc' hr
  let A := graph2 lookup (out.relabel j) (suc (cutoff.relabel j)) (gamma.relabel j)
  let B := graph2 lookup (out.relabel j) (cutoff.relabel j) (tail.relabel j)
  have hf : Nonempty (Derivation body (A :: Theta) B) := by
    have hhead := unaryRecover InternalListCodec.headCode drop (out.relabel j) rest
      (Fin.cons (suc (cutoff.relabel j)) (Fin.cons (gamma.relabel j) Fin.elim0))
      (show Nonempty (Derivation body (A :: Theta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hl A)
    exact lookupValue (out.relabel j) (cutoff.relabel j) (tail.relabel j) rest (withHyp hr A) hhead
  have hb : Nonempty (Derivation body (B :: Theta) A) := by
    have hhead := unaryRecover InternalListCodec.headCode drop (out.relabel j) rest
      (Fin.cons (cutoff.relabel j) (Fin.cons (tail.relabel j) Fin.elim0))
      (show Nonempty (Derivation body (B :: Theta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hr B)
    exact lookupValue (out.relabel j) (suc (cutoff.relabel j)) (gamma.relabel j) rest (withHyp hl B) hhead
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof

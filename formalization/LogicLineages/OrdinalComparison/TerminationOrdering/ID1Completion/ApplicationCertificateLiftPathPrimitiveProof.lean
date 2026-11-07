module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
open Source ApplicationCertificateLiftPath NumberedQuotientPathCertificates
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev Parameters := List Ty × Nat × Nat × Nat × Nat

attribute [local irreducible] Primrec

theorem vertexPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Parameters × Nat => vertex n arity p.1.1 p.1.2.1
      p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2) := by
  have hg : Primrec (fun p : Parameters × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : Parameters × Nat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hd : Primrec (fun p : Parameters × Nat => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have he : Primrec (fun p : Parameters × Nat => p.1.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ha : Primrec (fun p : Parameters × Nat => p.1.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ho := (JointGammaApplicationDecoderProof.decodedPrimitive n arity).comp
    (hg.pair (hc.pair (hd.pair (he.pair (Primrec.snd.pair ha)))))
  exact Primrec.option_getD.comp ho (Primrec.const 0)

attribute [local irreducible] vertex

theorem edgePrimitive {A : Type} [Primcodable A] {d e a c : A → Nat}
    (hd : Primrec d) (he : Primrec e) (ha : Primrec a) (hc : Primrec c) :
    Primrec (fun z => ApplicationCertificateLiftEdge.liftEdge (d z) (e z) (a z) (c z)) := by
  have hq : Primrec (fun z => ApplicationCertificateLiftEdge.sourceOf (c z)) :=
    Primrec.fst.comp (Primrec.unpair.comp hc)
  have hr : Primrec (fun z => ApplicationCertificateLiftEdge.targetOf (c z)) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hc)))
  have hs : Primrec (fun z => ApplicationCertificateLiftEdge.stepOf (c z)) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hc)))
  exact Primrec₂.natPair.comp (ApplicationCertificateLiftEdgeProof.applicationPrimitive hd he hq ha)
    (Primrec₂.natPair.comp (ApplicationCertificateLiftEdgeProof.applicationPrimitive hd he hr ha)
      (ApplicationCertificateLiftProof.actualPrimitive.2.1.comp hs))

theorem entryPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Parameters × EdgeEntry =>
      (vertex n arity p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2.1,
        ApplicationCertificateLiftEdge.liftEdge p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2.2)) := by
  have hv : Primrec (fun p : Parameters × EdgeEntry =>
      vertex n arity p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2.1) :=
    (vertexPrimitive n arity).comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hd : Primrec (fun p : Parameters × EdgeEntry => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have he : Primrec (fun p : Parameters × EdgeEntry => p.1.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ha : Primrec (fun p : Parameters × EdgeEntry => p.1.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hc : Primrec (fun p : Parameters × EdgeEntry => p.2.2) := Primrec.snd.comp Primrec.snd
  exact hv.pair (edgePrimitive hd he ha hc)

theorem entriesPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Parameters × List EdgeEntry =>
      liftEntries n arity p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2) :=
  Primrec.list_map Primrec.snd
    ((entryPrimitive n arity).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

attribute [local irreducible] liftEntries

theorem encoderPrimitive : Primrec pathCertificateNumber :=
  NumberedListCodecPrimrecProof.encoderPrimitive.comp
    (Primrec.list_map Primrec.id (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

theorem pathPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Parameters × Nat =>
      liftPath n arity p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 p.2) := by
  have hd : Primrec (fun p : Parameters × Nat => (decodePathCertificate p.2).getD []) :=
    Primrec.option_getD.comp
    (NumberedQuotientPathPrimrecSupportProof.pathCertificateDecoderPrimitive.comp Primrec.snd)
    (Primrec.const ([] : List EdgeEntry))
  unfold liftPath
  exact encoderPrimitive.comp ((entriesPrimitive n arity).comp (Primrec.fst.pair hd))

attribute [local irreducible] liftPath

theorem actualPrimitive : ApplicationCertificateLiftPathTargets.ActualPrimitive := by
  intro n arity
  have getP (i : Fin 5) : Primrec (fun v : List.Vector Nat 5 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have ho := JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp (getP 3)
  have hp : Primrec (fun p : List.Vector Nat 5 × ContextUniform.Object =>
      ((p.2.1,p.1.get 0,p.1.get 1,p.1.get 2,p.2.2),p.1.get 4)) :=
    ((Primrec.fst.comp Primrec.snd).pair (((getP 0).comp Primrec.fst).pair
      (((getP 1).comp Primrec.fst).pair (((getP 2).comp Primrec.fst).pair
        (Primrec.snd.comp Primrec.snd))))).pair ((getP 4).comp Primrec.fst)
  have hm := Primrec.option_map ho ((pathPrimitive n arity).comp hp).to₂
  exact Primrec.option_getD.comp hm (Primrec.const 0)

theorem actualProgramWitness : ApplicationCertificateLiftPathTargets.ActualProgramWitness := by
  intro n arity
  exact Proof.allPrimitiveFunctions 5 (pathValue n arity) (actualPrimitive n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof

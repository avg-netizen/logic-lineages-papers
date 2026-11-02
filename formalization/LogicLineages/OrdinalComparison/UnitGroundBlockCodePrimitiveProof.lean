module
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeTargets
public import LogicLineages.OrdinalComparison.OneUnitCodePrimitiveProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverNumericProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem application_primitive : Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+5) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 5)

private theorem probe_primitive : Primrec (fun p : Nat×Nat×Nat => probeCode p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hf : Primrec (fun p : Nat×Nat×Nat => OneUnitCode.firstCode p.1 1) :=
    OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.1.comp Primrec.fst (Primrec.const 1)
  have hu := OneUnitCode.Proof.primitiveRecursiveAlgorithms.1.comp hs
  have hv := Primrec.nat_mul.comp (Primrec.const 8) hx
  exact application_primitive.comp (hf.pair (application_primitive.comp (hu.pair hv)))

private theorem original_probe_primitive : Primrec₂ originalProbeCode := by
  have hs : Primrec (fun p : Nat×Nat => ContextInsertionCode.sourceCode 0 2 p.2) :=
    ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
      ((Primrec.const 0).pair ((Primrec.const 2).pair Primrec.snd))
  exact probe_primitive.comp (Primrec.fst.pair (hs.pair (Primrec.const 0)))

private theorem closed_probe_primitive : Primrec (fun p : Nat×Nat×Nat => closedProbeCode p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc := GroundClosingCode.Proof.primitiveRecursive.comp (Primrec.const 0) hs
  have hn : Primrec (fun p : Nat×Nat×Nat => p.1+2) :=
    Primrec.nat_add.comp Primrec.fst (Primrec.const 2)
  have hi := ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
    ((Primrec.const 0).pair (hn.pair hc))
  exact probe_primitive.comp (ht.pair (hi.pair (Primrec.const 1)))

private theorem build_primitive : Primrec (fun p : Nat×Nat×Nat => buildCode p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hf := OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.1.comp ht
  exact Primrec.fst.pair ((original_probe_primitive.comp ht hs).pair
    (closed_probe_primitive.pair (hf.pair (Primrec.fst.pair hs))))

private theorem anchor_computable : Computable anchorValue := by
  have hp : Computable (fun b : Payload (Nat×Nat) => b.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact AbsoluteObserver.Proof.open_evaluator_computable.comp hp

private theorem realize_computable : Computable realizeCode := by
  have hl : Computable (fun b : Payload (Nat×Nat) => b.2.1) := Computable.fst.comp Computable.snd
  have hr : Computable (fun b : Payload (Nat×Nat) => b.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hf : Computable (fun b : Payload (Nat×Nat) => b.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  exact Computable.fst.pair (hl.pair (hr.pair (hf.pair anchor_computable)))

theorem effectiveAlgorithms : Targets.EffectiveAlgorithms :=
  ⟨probe_primitive,original_probe_primitive,closed_probe_primitive,build_primitive,
    anchor_computable,realize_computable⟩
end LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Proof

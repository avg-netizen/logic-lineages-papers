module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedMarkCertificate
open NumberedFiniteMarkPrimrec NumberedCodeView NumberedHeadCodecPrimrecSupportProof

attribute [local irreducible] Primrec

theorem finiteMarkCodeCalibration :
    NumberedFiniteMarkPrimrecTargets.ActualFiniteMarkCodeCalibration := by
  intro Symbol arity Gamma tau label q
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  all_goals simp_all [finiteMarkCode, finiteMark, termCode, argumentsCode,
    NumberedAuxiliaryDecodingProof.headRoundTrip, Option.map_map, Function.comp_def]

private def lambdaType {Symbol : Type} : Code Symbol → Option Ty
  | .lam sigma _ => some sigma
  | _ => none

private def viewLambdaType (n : Nat) : CodeView n → Option Ty :=
  Sum.elim (fun _ => none)
    (Sum.elim (fun p : Ty × Code (Fin n) => some p.1) (fun _ => none))

private theorem lambdaTypePrimitive (n : Nat) : Primrec (@lambdaType (Fin n)) := by
  have h : Primrec (viewLambdaType n) :=
    sumElim (Primrec.const none)
      (sumElim (Primrec.option_some.comp Primrec.fst) (Primrec.const none))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq
    (by intro code; cases code <;> rfl)

private abbrev MarkContext (n : Nat) :=
  Nat × (Code (Fin n) × List (Option (Code (Fin n))))

private def recombine {n : Nat} (label : Nat)
    (p : Code (Fin n) × List (Option (Code (Fin n)))) : Option (Option (Code (Fin n))) :=
  some (Option.casesOn (lambdaType p.1)
    ((NumberedDirectCodePrimrecProof.ordinaryParts p.1).map (fun fields =>
      Code.numbered label fields.1 (headResult (decodeHead fields.1)) fields.2 [] .argumentsNil))
    (fun sigma => (p.2.getD 0 none).map (Code.lam sigma)))

private theorem recombinePrimitive (n : Nat) : Primrec₂ (@recombine n) := by
  have hhead : Primrec (fun p : MarkContext n × (HeadCode (Fin n) × Code (Fin n)) =>
      p.2.1) := Primrec.fst.comp Primrec.snd
  have hnode : Primrec (fun p : MarkContext n × (HeadCode (Fin n) × Code (Fin n)) =>
      Code.numbered p.1.1 p.2.1 (headResult (decodeHead p.2.1)) p.2.2 [] .argumentsNil) :=
    (NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp
      ((Primrec.fst.comp Primrec.fst).pair (hhead.pair
        (((NumberedHeadSignaturePrimrecProof.headResultPrimitive n).comp hhead).pair
          ((Primrec.snd.comp Primrec.snd).pair
            ((Primrec.const []).pair (Primrec.const Code.argumentsNil))))))
  have hordinary : Primrec (fun p : MarkContext n =>
      (NumberedDirectCodePrimrecProof.ordinaryParts p.2.1).map (fun fields =>
        Code.numbered p.1 fields.1 (headResult (decodeHead fields.1)) fields.2 [] .argumentsNil)) :=
    Primrec.option_map
      ((NumberedDirectCodePrimrecProof.ordinaryPartsPrimitive n).comp
        (Primrec.fst.comp Primrec.snd)) hnode.to₂
  have hchild : Primrec (fun p : MarkContext n × Ty => p.1.2.2.getD 0 none) :=
    (Primrec.list_getD (none : Option (Code (Fin n)))).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 0)
  have hlam : Primrec (fun p : (MarkContext n × Ty) × Code (Fin n) =>
      Code.lam p.1.2 p.2) :=
    (NumberedCodeAssemblyPrimrecProof.lamPrimitive n).comp
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hlambda : Primrec (fun p : MarkContext n × Ty =>
      (p.1.2.2.getD 0 none).map (Code.lam p.2)) :=
    Primrec.option_map hchild hlam.to₂
  exact (Primrec.option_some.comp (Primrec.option_casesOn
    (o := fun p : MarkContext n => lambdaType p.2.1)
    (f := fun p : MarkContext n =>
      (NumberedDirectCodePrimrecProof.ordinaryParts p.2.1).map (fun fields =>
        Code.numbered p.1 fields.1 (headResult (decodeHead fields.1)) fields.2 [] .argumentsNil))
    (g := fun (p : MarkContext n) (sigma : Ty) =>
      (p.2.2.getD 0 none).map (Code.lam sigma))
    ((lambdaTypePrimitive n).comp (Primrec.fst.comp Primrec.snd))
    hordinary hlambda.to₂)).to₂

private theorem recombineCalibration (n label : Nat) (code : Code (Fin n)) :
    recombine label (code,
      (NumberedSyntaxBoundsPrimrecSupportProof.children code).map (finiteMarkCode label)) =
        some (finiteMarkCode label code) := by
  cases code <;> simp [recombine, lambdaType, NumberedDirectCodePrimrecProof.ordinaryParts,
    NumberedSyntaxBoundsPrimrecSupportProof.children, finiteMarkCode]

theorem finiteMarkCodePrimitive :
    NumberedFiniteMarkPrimrecTargets.ActualFiniteMarkCodePrimitive := by
  intro n
  exact Primrec.nat_omega_rec (fun label (code : Code (Fin n)) => finiteMarkCode label code)
    (m := fun (_ : Nat) code => NumberedLeastCodeRepresentative.codeNumber code)
    (l := fun (_ : Nat) code => NumberedSyntaxBoundsPrimrecSupportProof.children code)
    (g := @recombine n)
    (((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd).to₂)
    (((NumberedSyntaxBoundsPrimrecSupportProof.childrenPrimitive n).comp Primrec.snd).to₂)
    (recombinePrimitive n)
    (fun _ => NumberedSyntaxBoundsPrimrecSupportProof.childrenDecrease n)
    (recombineCalibration n)

theorem markTargetPrimitive : NumberedFiniteMarkPrimrecTargets.ActualMarkTargetPrimitive := by
  intro n arity Gamma
  have hcode : Primrec (fun p : Nat × Packed (Fin n) arity Gamma => termCode p.2.2) :=
    Primrec.snd.comp
      ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp Primrec.snd)
  have hr : Primrec (fun p : Nat × Packed (Fin n) arity Gamma =>
      finiteMarkCode p.1 (termCode p.2.2)) :=
    (finiteMarkCodePrimitive n).comp (Primrec.fst.pair hcode)
  apply NumberedDirectOperationsProof.reconstructSameType Prod.snd
    (fun p : Nat × Packed (Fin n) arity Gamma => markTarget p.1 p.2)
    (fun p : Nat × Packed (Fin n) arity Gamma => finiteMarkCode p.1 (termCode p.2.2))
    Primrec.snd hr
  · intro p
    simpa only [markTarget, Option.map_map, Function.comp_def] using
      finiteMarkCodeCalibration (Fin n) arity Gamma p.2.1 p.1 p.2.2
  · intro p r h
    obtain ⟨s, _, hs⟩ := Option.map_eq_some_iff.mp h
    cases hs
    rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecProof

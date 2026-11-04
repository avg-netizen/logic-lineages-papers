module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedAuxiliaryCoding NumberedOriginalSourceCodec NumberedOriginalSourceShape
open NumberedLeastCodeRepresentative NumberedCodeView NumberedSyntaxBoundsPrimrecSupportProof
open NumberedHeadCodecPrimrecSupportProof

theorem pureBindIsSome {alpha beta : Type} (o : Option alpha) (f : alpha → beta) :
    (o.bind (fun a => some (f a))).isSome=o.isSome := by
  cases o <;> rfl

theorem termShape : NumberedOriginalSourceShapeTargets.ActualTermShape := by
  intro Symbol arity Gamma tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => (projectArguments args).isSome=codeShape (argumentsCode args))
  case var => rfl
  case lam body ih => simpa only [project,termCode,codeShape,Option.isSome_map] using ih
  case app => rfl
  case bottom => rfl
  case numbered => rfl
  case ordinary f base ih =>
    cases f with
    | zero => cases base; rfl
    | succ => cases base; rfl
    | cases tau => cases base; rfl
    | recursor tau => cases base; rfl
    | application sigma tau =>
      dsimp only [headArguments,headResult] at base ih ⊢
      have hp : (project (AuxTerm.ordinary (.application sigma tau) base)).isSome=(projectArguments base).isSome := by
        change ((projectArguments base).bind (fun values => match values with
          | .cons f (.cons a .nil) => some (Term.app f a))).isSome=(projectArguments base).isSome
        cases hb : projectArguments base with
        | none => rfl
        | some values => cases values with
          | cons f rest => cases rest with
            | cons a rest => cases rest; rfl
      exact hp.trans ih
    | ranked f =>
      dsimp only [headArguments,headResult] at base ih ⊢
      change ((projectArguments base).bind (fun values => some (Term.ranked f (groundValues (arity f) values)))).isSome=
        codeShape (argumentsCode base)
      exact (pureBindIsSome (projectArguments base) (fun values => Term.ranked f (groundValues (arity f) values))).trans ih
  case nil => rfl
  case cons q rest ihq ihr =>
    have hp : (projectArguments (AuxArguments.cons q rest)).isSome=((project q).isSome && (projectArguments rest).isSome) := by
      cases hq : project q <;> cases hr : projectArguments rest <;> simp [projectArguments,hq,hr]
    exact hp.trans (congrArg₂ Bool.and ihq ihr)

theorem argumentsShape : NumberedOriginalSourceShapeTargets.ActualArgumentsShape := by
  intro Symbol arity Gamma types args
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest =>
      have hp : (projectArguments (AuxArguments.cons q rest)).isSome=((project q).isSome && (projectArguments rest).isSome) := by
        cases hq : project q <;> cases hr : projectArguments rest <;> simp [projectArguments,hq,hr]
      exact hp.trans (congrArg₂ Bool.and (termShape Symbol arity Gamma sigma q) (ih rest))

def rootShape {Symbol : Type} : Code Symbol → Bool
  | .app _ _ _ | .bottom _ | .numbered _ _ _ _ _ _ => false
  | _ => true

def viewRootShape (n : Nat) : CodeView n → Bool :=
  Sum.elim (fun _ : Nat => true)
    (Sum.elim (fun _ : Ty × Code (Fin n) => true)
      (Sum.elim (fun _ : Ty × Code (Fin n) × Code (Fin n) => false)
        (Sum.elim (fun _ : Ty => false)
          (Sum.elim (fun _ : HeadCode (Fin n) × Code (Fin n) => true)
            (Sum.elim (fun _ : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) => false)
              (Sum.elim (fun _ : Unit => true)
                (fun _ : Ty × Code (Fin n) × Code (Fin n) => true)))))))

theorem viewRootShapePrimitive (n : Nat) : Primrec (viewRootShape n) := by
  unfold viewRootShape
  apply sumElim (Primrec.const true)
  apply sumElim (Primrec.const true)
  apply sumElim (Primrec.const false)
  apply sumElim (Primrec.const false)
  apply sumElim (Primrec.const true)
  apply sumElim (Primrec.const false)
  exact sumElim (Primrec.const true) (Primrec.const true)

theorem rootShapePrimitive (n : Nat) : Primrec (@rootShape (Fin n)) :=
  ((viewRootShapePrimitive n).comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

def collectShape (values : List Bool) : Bool := values.foldr Bool.and true

def recombine {Symbol : Type} (code : Code Symbol) (values : List Bool) : Option Bool :=
  some (rootShape code && collectShape values)

theorem collectShapePrimitive : Primrec collectShape := by
  unfold collectShape
  have hm : Primrec (fun p : Bool × Bool => p.1 && p.2) := Primrec.and
  exact Primrec.list_foldr Primrec.id (Primrec.const true) (hm.comp Primrec.snd).to₂

theorem recombinePrimitive (n : Nat) : Primrec₂ (@recombine (Fin n)) :=
  (Primrec.option_some.comp (Primrec.and.comp ((rootShapePrimitive n).comp Primrec.fst)
    (collectShapePrimitive.comp Primrec.snd))).to₂

theorem recombineCalibration {Symbol : Type} (code : Code Symbol) :
    recombine code ((children code).map codeShape)=some (codeShape code) := by
  cases code <;> simp [recombine,rootShape,collectShape,children,codeShape]

theorem codeShapePrimitive : NumberedOriginalSourceShapeTargets.ActualCodeShapePrimitive := by
  intro n
  exact Primrec.nat_omega_rec' (@codeShape (Fin n)) (m := @codeNumber n) (l := @children (Fin n)) (g := @recombine (Fin n))
    (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n) (childrenPrimitive n) (recombinePrimitive n)
    (childrenDecrease n) recombineCalibration

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeProof

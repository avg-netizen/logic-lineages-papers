module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCodePrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecSupportProof
open Source NumberedAuxiliaryCoding NumberedExchangeCode NumberedTypedFocus NumberedNumericStep
open NumberedFocusCode NumberedExchangeCodeFieldsProof
open NumberedRequestExpansionPrimrecSupportProof

attribute [local irreducible] Primrec

theorem entriesCodePrimitive (n : Nat) : Primrec (@entriesCode (Fin n)) := by
  have hstep : Primrec₂ (fun (_ : List (Ty × Code (Fin n)))
      (p : (Ty × Code (Fin n)) × Code (Fin n)) => Code.argumentsCons p.1.1 p.1.2 p.2) :=
    ((NumberedCodeAssemblyPrimrecProof.argumentsConsPrimitive n).comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.snd.comp Primrec.snd)))).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const Code.argumentsNil) hstep).of_eq
    (by
      intro entries
      induction entries with
      | nil => rfl
      | cons entry entries ih =>
        rcases entry with ⟨tau, q⟩
        change Code.argumentsCons tau q
          (entries.foldr (fun entry rest => Code.argumentsCons entry.1 entry.2 rest) .argumentsNil) =
            Code.argumentsCons tau q (entriesCode entries)
        exact congrArg (Code.argumentsCons tau q) (by simpa only [id_eq] using ih))

theorem argumentAtPrimitive (n : Nat) :
    Primrec (fun p : List Ty × Nat × Code (Fin n) => argumentAt p.1 p.2.1 p.2.2) := by
  let Input := List Ty × Nat × Code (Fin n)
  let Entry := Ty × Code (Fin n)
  have hselected : Primrec (fun p : Input × List Entry =>
      (p.2[p.1.2.1]?).bind (fun selected => some (p.1.1, selected.1, selected.2))) :=
    Primrec.option_bind
      (Primrec.list_getElem?.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.option_some.comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂
  exact Primrec.option_bind
    ((NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n).comp
      (Primrec.snd.comp Primrec.snd)) hselected.to₂

private def descentProgram {n : Nat} (p : Position × RawValue (Fin n)) :
    Option (RawValue (Fin n)) :=
  let position := Nat.unpair (positionNumber p.1)
  let data := fields p.2.2.2
  if position.1 = 0 then
    if data.1 = 1 then
      (arrowParts p.2.2.1).bind (fun types =>
        if data.2.1 = types.1 then
          some (data.2.1 :: p.2.1, types.2, data.2.2.2.2.2.1) else none)
    else none
  else if position.1 = 1 then
    if data.1 = 2 then some (p.2.1, Ty.arrow data.2.1 p.2.2.1, data.2.2.2.2.2.1) else none
  else if position.1 = 2 then
    if data.1 = 4 then argumentAt p.2.1 position.2 data.2.2.2.2.2.1 else none
  else if position.1 = 3 then
    if data.1 = 5 then argumentAt p.2.1 position.2 data.2.2.2.2.2.1 else none
  else if position.1 = 4 then
    if data.1 = 5 then argumentAt p.2.1 position.2 data.2.2.2.2.2.2 else none
  else none

private theorem descentProgramPrimitive (n : Nat) : Primrec (@descentProgram n) := by
  let Input := Position × RawValue (Fin n)
  have hposition : Primrec (fun p : Input => Nat.unpair (positionNumber p.1)) :=
    Primrec.unpair.comp (NumberedStepCodecPrimrecProof.positionEncoderPrimitive.comp Primrec.fst)
  have htag := Primrec.fst.comp hposition
  have hindex := Primrec.snd.comp hposition
  have hGamma : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have htau : Primrec (fun p : Input => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : Input => fields p.2.2.2) :=
    (fieldsPrimitive n).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hconstructor := Primrec.fst.comp hd
  have hsigma := Primrec.fst.comp (Primrec.snd.comp hd)
  have hchildren := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp hd))))
  have hfirst := Primrec.fst.comp hchildren
  have hsecond := Primrec.snd.comp hchildren
  have hlamBody : Primrec (fun p : Input × (Ty × Ty) =>
      if (fields p.1.2.2.2).2.1 = p.2.1 then
        some ((fields p.1.2.2.2).2.1 :: p.1.2.1, p.2.2, (fields p.1.2.2.2).2.2.2.2.2.1)
      else none) :=
    Primrec.ite (Primrec.eq.comp (hsigma.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.option_some.comp
        ((Primrec.list_cons.comp (hsigma.comp Primrec.fst) (hGamma.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.snd).pair (hfirst.comp Primrec.fst))))
      (Primrec.const none)
  have hlam : Primrec (fun p : Input =>
      (arrowParts p.2.2.1).bind (fun types =>
        if (fields p.2.2.2).2.1 = types.1 then
          some ((fields p.2.2.2).2.1 :: p.2.1, types.2, (fields p.2.2.2).2.2.2.2.2.1)
        else none)) :=
    Primrec.option_bind (arrowPartsPrimitive.comp htau) hlamBody.to₂
  have happ : Primrec (fun p : Input =>
      some (p.2.1, Ty.arrow (fields p.2.2.2).2.1 p.2.2.1, (fields p.2.2.2).2.2.2.2.2.1)) :=
    Primrec.option_some.comp
      (hGamma.pair ((NumberedHeadSignaturePrimrecProof.arrowPrimitive.comp hsigma htau).pair hfirst))
  have hbase : Primrec (fun p : Input =>
      argumentAt p.2.1 (Nat.unpair (positionNumber p.1)).2 (fields p.2.2.2).2.2.2.2.2.1) :=
    (argumentAtPrimitive n).comp (hGamma.pair (hindex.pair hfirst))
  have hextras : Primrec (fun p : Input =>
      argumentAt p.2.1 (Nat.unpair (positionNumber p.1)).2 (fields p.2.2.2).2.2.2.2.2.2) :=
    (argumentAtPrimitive n).comp (hGamma.pair (hindex.pair hsecond))
  have htagEq (k : Nat) : PrimrecPred (fun p : Input => (Nat.unpair (positionNumber p.1)).1 = k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hconstructorEq (k : Nat) : PrimrecPred (fun p : Input => (fields p.2.2.2).1 = k) :=
    Primrec.eq.comp hconstructor (Primrec.const k)
  exact Primrec.ite (htagEq 0) (Primrec.ite (hconstructorEq 1) hlam (Primrec.const none))
    (Primrec.ite (htagEq 1) (Primrec.ite (hconstructorEq 2) happ (Primrec.const none))
      (Primrec.ite (htagEq 2) (Primrec.ite (hconstructorEq 4) hbase (Primrec.const none))
        (Primrec.ite (htagEq 3) (Primrec.ite (hconstructorEq 5) hbase (Primrec.const none))
          (Primrec.ite (htagEq 4) (Primrec.ite (hconstructorEq 5) hextras (Primrec.const none))
            (Primrec.const none)))))

theorem descendPrimitive (n : Nat) :
    Primrec (fun p : Position × RawValue (Fin n) => descendCode p.1 p.2) := by
  apply (descentProgramPrimitive n).of_eq
  rintro ⟨position, Gamma, tau, code⟩
  cases position <;> cases code <;> cases tau <;>
    simp [descentProgram, descendCode, fields, positionNumber, arrowParts]

theorem replaceArgumentPrimitive (n : Nat) :
    Primrec (fun p : Nat × Code (Fin n) × Code (Fin n) =>
      replaceArgumentCode p.1 p.2.1 p.2.2) := by
  let Input := Nat × Code (Fin n) × Code (Fin n)
  let Entry := Ty × Code (Fin n)
  have hupdate : Primrec (fun p : (Input × List Entry) × Entry =>
      some (entriesCode (p.1.2.set p.1.1.1 (p.2.1, p.1.1.2.2)))) :=
    Primrec.option_some.comp ((entriesCodePrimitive n).comp
      (Primrec.list_set.comp (Primrec.snd.comp Primrec.fst)
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.fst.comp Primrec.snd).pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))))
  have hselected : Primrec (fun p : Input × List Entry =>
      (p.2[p.1.1]?).bind (fun selected =>
        some (entriesCode (p.2.set p.1.1 (selected.1, p.1.2.2))))) :=
    Primrec.option_bind
      (Primrec.list_getElem?.comp Primrec.snd (Primrec.fst.comp Primrec.fst)) hupdate.to₂
  exact Primrec.option_bind
    ((NumberedExchangeRootPrimrecProof.argumentEntriesPrimitive n).comp
      (Primrec.fst.comp Primrec.snd)) hselected.to₂

private def wrapProgram {n : Nat} (p : Frame (Fin n) × Code (Fin n)) : Option (Code (Fin n)) :=
  let position := Nat.unpair (positionNumber p.1.1)
  let data := fields p.1.2
  if position.1 = 0 then
    if data.1 = 1 then some (.lam data.2.1 p.2) else none
  else if position.1 = 1 then
    if data.1 = 2 then some (.app data.2.1 p.2 data.2.2.2.2.2.2) else none
  else if position.1 = 2 then
    if data.1 = 4 then
      (replaceArgumentCode position.2 data.2.2.2.2.2.1 p.2).map (Code.ordinary data.2.2.1)
    else none
  else if position.1 = 3 then
    if data.1 = 5 then
      (replaceArgumentCode position.2 data.2.2.2.2.2.1 p.2).map (fun target =>
        .numbered data.2.2.2.1 data.2.2.1 data.2.1 target data.2.2.2.2.1 data.2.2.2.2.2.2)
    else none
  else if position.1 = 4 then
    if data.1 = 5 then
      (replaceArgumentCode position.2 data.2.2.2.2.2.2 p.2).map (fun target =>
        .numbered data.2.2.2.1 data.2.2.1 data.2.1 data.2.2.2.2.2.1 data.2.2.2.2.1 target)
    else none
  else none

private theorem wrapProgramPrimitive (n : Nat) : Primrec (@wrapProgram n) := by
  let Input := Frame (Fin n) × Code (Fin n)
  have hposition : Primrec (fun p : Input => Nat.unpair (positionNumber p.1.1)) :=
    Primrec.unpair.comp
      (NumberedStepCodecPrimrecProof.positionEncoderPrimitive.comp (Primrec.fst.comp Primrec.fst))
  have htag := Primrec.fst.comp hposition
  have hindex := Primrec.snd.comp hposition
  have hd : Primrec (fun p : Input => fields p.1.2) :=
    (fieldsPrimitive n).comp (Primrec.snd.comp Primrec.fst)
  have hconstructor := Primrec.fst.comp hd
  have htype := Primrec.fst.comp (Primrec.snd.comp hd)
  have hhead := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hd))
  have hlabel := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hd)))
  have htypes := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp hd))))
  have hchildren := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp hd))))
  have hfirst := Primrec.fst.comp hchildren
  have hsecond := Primrec.snd.comp hchildren
  have hlam : Primrec (fun p : Input => some (Code.lam (fields p.1.2).2.1 p.2)) :=
    Primrec.option_some.comp ((NumberedCodeAssemblyPrimrecProof.lamPrimitive n).comp
      (htype.pair Primrec.snd))
  have happ : Primrec (fun p : Input =>
      some (Code.app (fields p.1.2).2.1 p.2 (fields p.1.2).2.2.2.2.2.2)) :=
    Primrec.option_some.comp ((NumberedCodeAssemblyPrimrecProof.appPrimitive n).comp
      (htype.pair (Primrec.snd.pair hsecond)))
  have hbase : Primrec (fun p : Input =>
      replaceArgumentCode (Nat.unpair (positionNumber p.1.1)).2 (fields p.1.2).2.2.2.2.2.1 p.2) :=
    (replaceArgumentPrimitive n).comp (hindex.pair (hfirst.pair Primrec.snd))
  have hextras : Primrec (fun p : Input =>
      replaceArgumentCode (Nat.unpair (positionNumber p.1.1)).2 (fields p.1.2).2.2.2.2.2.2 p.2) :=
    (replaceArgumentPrimitive n).comp (hindex.pair (hsecond.pair Primrec.snd))
  have hordinaryNode : Primrec (fun p : Input × Code (Fin n) =>
      Code.ordinary (fields p.1.1.2).2.2.1 p.2) :=
    (NumberedCodeAssemblyPrimrecProof.ordinaryPrimitive n).comp
      ((hhead.comp Primrec.fst).pair Primrec.snd)
  have hbaseNode : Primrec (fun p : Input × Code (Fin n) =>
      Code.numbered (fields p.1.1.2).2.2.2.1 (fields p.1.1.2).2.2.1 (fields p.1.1.2).2.1
        p.2 (fields p.1.1.2).2.2.2.2.1 (fields p.1.1.2).2.2.2.2.2.2) :=
    (NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp
      ((hlabel.comp Primrec.fst).pair ((hhead.comp Primrec.fst).pair
        ((htype.comp Primrec.fst).pair
          (Primrec.snd.pair ((htypes.comp Primrec.fst).pair (hsecond.comp Primrec.fst))))))
  have hextrasNode : Primrec (fun p : Input × Code (Fin n) =>
      Code.numbered (fields p.1.1.2).2.2.2.1 (fields p.1.1.2).2.2.1 (fields p.1.1.2).2.1
        (fields p.1.1.2).2.2.2.2.2.1 (fields p.1.1.2).2.2.2.2.1 p.2) :=
    (NumberedCodeAssemblyPrimrecProof.numberedPrimitive n).comp
      ((hlabel.comp Primrec.fst).pair ((hhead.comp Primrec.fst).pair
        ((htype.comp Primrec.fst).pair
          ((hfirst.comp Primrec.fst).pair ((htypes.comp Primrec.fst).pair Primrec.snd)))))
  have hordinary := Primrec.option_map hbase hordinaryNode.to₂
  have hnumberedBase := Primrec.option_map hbase hbaseNode.to₂
  have hnumberedExtras := Primrec.option_map hextras hextrasNode.to₂
  have htagEq (k : Nat) : PrimrecPred (fun p : Input => (Nat.unpair (positionNumber p.1.1)).1 = k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hconstructorEq (k : Nat) : PrimrecPred (fun p : Input => (fields p.1.2).1 = k) :=
    Primrec.eq.comp hconstructor (Primrec.const k)
  exact Primrec.ite (htagEq 0) (Primrec.ite (hconstructorEq 1) hlam (Primrec.const none))
    (Primrec.ite (htagEq 1) (Primrec.ite (hconstructorEq 2) happ (Primrec.const none))
      (Primrec.ite (htagEq 2) (Primrec.ite (hconstructorEq 4) hordinary (Primrec.const none))
        (Primrec.ite (htagEq 3) (Primrec.ite (hconstructorEq 5) hnumberedBase (Primrec.const none))
          (Primrec.ite (htagEq 4) (Primrec.ite (hconstructorEq 5) hnumberedExtras (Primrec.const none))
            (Primrec.const none)))))

theorem wrapPrimitive (n : Nat) :
    Primrec (fun p : Frame (Fin n) × Code (Fin n) => wrapCode p.1 p.2) := by
  apply (wrapProgramPrimitive n).of_eq
  rintro ⟨⟨position, code⟩, replacement⟩
  cases position <;> cases code <;> simp [wrapProgram, wrapCode, fields, positionNumber]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecSupportProof

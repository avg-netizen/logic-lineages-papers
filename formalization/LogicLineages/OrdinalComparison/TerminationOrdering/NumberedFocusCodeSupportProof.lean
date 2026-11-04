module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
  NumberedExchangeCode NumberedStepContexts NumberedTypedFocus NumberedFocusCode
open NumberedExchangeCalibrationSupportProof

theorem focusCode_nil {Symbol : Type} (Gamma : List Ty) (tau : Ty) (code : Code Symbol) :
    focusCode [] Gamma tau code = some (Gamma, tau, code) := rfl

theorem focusCode_cons {Symbol : Type} (position : Position) (path : List Position)
    (Gamma : List Ty) (tau : Ty) (code : Code Symbol) :
    focusCode (position :: path) Gamma tau code =
      (descendCode position (Gamma, tau, code)).bind
        (fun child => focusCode path child.1 child.2.1 child.2.2) := by
  cases hd : descendCode position (Gamma, tau, code) with
  | none => simp [focusCode, traceCode, hd]
  | some child =>
    cases ht : traceCode path child with
    | none => simp [focusCode, traceCode, hd, ht]
    | some result => simp [focusCode, traceCode, hd, ht]

theorem unwind_append_singleton {Symbol : Type} (frames : List (Frame Symbol))
    (frame : Frame Symbol) (replacement : Code Symbol) :
    unwindCode (frames ++ [frame]) replacement =
      (unwindCode frames replacement).bind (wrapCode frame) := by
  simp only [unwindCode, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem replaceCode_nil {Symbol : Type} (Gamma : List Ty) (tau : Ty)
    (code replacement : Code Symbol) :
    replaceCode [] Gamma tau code replacement = some replacement := rfl

theorem replaceCode_cons {Symbol : Type} (position : Position) (path : List Position)
    (Gamma : List Ty) (tau : Ty) (code replacement : Code Symbol) :
    replaceCode (position :: path) Gamma tau code replacement =
      (descendCode position (Gamma, tau, code)).bind (fun child =>
        (replaceCode path child.1 child.2.1 child.2.2 replacement).bind
          (wrapCode (position, code))) := by
  simp only [replaceCode, traceCode, Option.bind_eq_bind, Option.pure_def,
    Option.bind_assoc, Option.bind_some, unwind_append_singleton]

theorem entriesCodeCalibration {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} (args : AuxArguments Symbol arity Gamma types) :
    entriesCode ((argumentList args).map packedCode) = argumentsCode args := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih =>
    cases args with
    | cons q rest => simp [argumentList, entriesCode, packedCode, argumentsCode, ih rest]

theorem argumentAtCalibration {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} (index : Nat) (args : AuxArguments Symbol arity Gamma types) :
    argumentAt Gamma index (argumentsCode args) =
      ((argumentList args)[index]?).map (fun q => (Gamma, q.1, termCode q.2)) := by
  simp only [argumentAt, argumentEntriesCalibration, Option.bind_eq_bind,
    Option.bind_some, List.getElem?_map]
  cases h : (argumentList args)[index]? <;> simp [h, packedCode]

theorem argumentAt_zero {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    {sigma : Ty} (q : AuxTerm Symbol arity Gamma sigma)
    (rest : AuxArguments Symbol arity Gamma types) :
    argumentAt Gamma 0 (argumentsCode (.cons q rest)) = some (Gamma, sigma, termCode q) := by
  simp [argumentAtCalibration, argumentList]

theorem argumentAt_succ {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    {sigma : Ty} (index : Nat) (q : AuxTerm Symbol arity Gamma sigma)
    (rest : AuxArguments Symbol arity Gamma types) :
    argumentAt Gamma (index + 1) (argumentsCode (.cons q rest)) =
      argumentAt Gamma index (argumentsCode rest) := by
  simp [argumentAtCalibration, argumentList]

theorem replaceArgumentCode_zero {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} {sigma : Ty} (q : AuxTerm Symbol arity Gamma sigma)
    (rest : AuxArguments Symbol arity Gamma types) (replacement : Code Symbol) :
    replaceArgumentCode 0 (argumentsCode (.cons q rest)) replacement =
      some (.argumentsCons sigma replacement (argumentsCode rest)) := by
  simp [replaceArgumentCode, argumentEntriesCalibration, argumentList, packedCode,
    entriesCode, entriesCodeCalibration]

theorem replaceArgumentCode_succ {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} {sigma : Ty} (index : Nat) (q : AuxTerm Symbol arity Gamma sigma)
    (rest : AuxArguments Symbol arity Gamma types) (replacement : Code Symbol) :
    replaceArgumentCode (index + 1) (argumentsCode (.cons q rest)) replacement =
      (replaceArgumentCode index (argumentsCode rest) replacement).map
        (Code.argumentsCons sigma (termCode q)) := by
  simp only [replaceArgumentCode, argumentEntriesCalibration, argumentList,
    List.map_cons, Option.bind_eq_bind, Option.bind_some, List.getElem?_cons_succ]
  cases h : ((argumentList rest).map packedCode)[index]? <;>
    simp [h, List.set_cons_succ, entriesCode, packedCode]

def replaceArgumentFocus {Symbol : Type} (path : List Position) (Gamma : List Ty)
    (index : Nat) (args replacement : Code Symbol) : Option (Code Symbol) :=
  (argumentAt Gamma index args).bind (fun child =>
    (replaceCode path child.1 child.2.1 child.2.2 replacement).bind
      (fun result => replaceArgumentCode index args result))

theorem replaceArgumentFocus_zero {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} {sigma : Ty} (path : List Position)
    (q : AuxTerm Symbol arity Gamma sigma) (rest : AuxArguments Symbol arity Gamma types)
    (replacement : Code Symbol) :
    replaceArgumentFocus path Gamma 0 (argumentsCode (.cons q rest)) replacement =
      (replaceCode path Gamma sigma (termCode q) replacement).map
        (fun result => Code.argumentsCons sigma result (argumentsCode rest)) := by
  simp only [replaceArgumentFocus, argumentAt_zero, Option.bind_some,
    replaceArgumentCode_zero, Option.map_eq_bind, Function.comp_def]

theorem replaceArgumentFocus_succ {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} {sigma : Ty} (path : List Position) (index : Nat)
    (q : AuxTerm Symbol arity Gamma sigma) (rest : AuxArguments Symbol arity Gamma types)
    (replacement : Code Symbol) :
    replaceArgumentFocus path Gamma (index + 1) (argumentsCode (.cons q rest)) replacement =
      (replaceArgumentFocus path Gamma index (argumentsCode rest) replacement).map
        (Code.argumentsCons sigma (termCode q)) := by
  simp only [replaceArgumentFocus, argumentAt_succ, replaceArgumentCode_succ,
    Option.map_bind, Function.comp_def]

theorem replaceCode_lam {Symbol : Type} (path : List Position) (Gamma : List Ty)
    (sigma tau : Ty) (body replacement : Code Symbol) :
    replaceCode (.lam :: path) Gamma (.arrow sigma tau) (.lam sigma body) replacement =
      (replaceCode path (sigma :: Gamma) tau body replacement).map (Code.lam sigma) := by
  simp [replaceCode_cons, descendCode, wrapCode, Option.map_eq_bind]

theorem replaceCode_app {Symbol : Type} (path : List Position) (Gamma : List Ty)
    (sigma tau : Ty) (fn arg replacement : Code Symbol) :
    replaceCode (.appFunction :: path) Gamma tau (.app sigma fn arg) replacement =
      (replaceCode path Gamma (.arrow sigma tau) fn replacement).map
        (fun result => Code.app sigma result arg) := by
  simp [replaceCode_cons, descendCode, wrapCode, Option.map_eq_bind]

theorem replaceCode_ordinary {Symbol : Type} (path : List Position) (Gamma : List Ty)
    (tau : Ty) (index : Nat) (head : HeadCode Symbol) (base replacement : Code Symbol) :
    replaceCode (.ordinaryBase index :: path) Gamma tau (.ordinary head base) replacement =
      (replaceArgumentFocus path Gamma index base replacement).map (Code.ordinary head) := by
  simp only [replaceCode_cons, descendCode, wrapCode, replaceArgumentFocus,
    Option.map_bind, Function.comp_def]

theorem replaceCode_numberedBase {Symbol : Type} (path : List Position) (Gamma : List Ty)
    (tau result : Ty) (index label : Nat) (head : HeadCode Symbol)
    (base : Code Symbol) (types : List Ty) (extras replacement : Code Symbol) :
    replaceCode (.numberedBase index :: path) Gamma tau
      (.numbered label head result base types extras) replacement =
      (replaceArgumentFocus path Gamma index base replacement).map
        (fun target => Code.numbered label head result target types extras) := by
  simp only [replaceCode_cons, descendCode, wrapCode, replaceArgumentFocus,
    Option.map_bind, Function.comp_def]

theorem replaceCode_numberedExtras {Symbol : Type} (path : List Position) (Gamma : List Ty)
    (tau result : Ty) (index label : Nat) (head : HeadCode Symbol)
    (base : Code Symbol) (types : List Ty) (extras replacement : Code Symbol) :
    replaceCode (.numberedExtras index :: path) Gamma tau
      (.numbered label head result base types extras) replacement =
      (replaceArgumentFocus path Gamma index extras replacement).map
        (fun target => Code.numbered label head result base types target) := by
  simp only [replaceCode_cons, descendCode, wrapCode, replaceArgumentFocus,
    Option.map_bind, Function.comp_def]

def termFocusValue {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (f : TermFocus n arity Gamma tau) : RawValue (Fin n) :=
  (f.holeGamma, f.holeType, termCode f.value)

def argumentFocusValue {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
    (f : ArgumentFocus n arity Gamma types) : RawValue (Fin n) :=
  (f.holeGamma, f.holeType, termCode f.value)

theorem argumentFocusValueCalibration {n : Nat} {arity : Fin n → Nat}
    (path : List Position) (Gamma : List Ty)
    (hvisit : ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
      focusCode path Gamma tau (termCode q) = (focus path q).map termFocusValue)
    {types : List Ty} (index : Nat) (args : AuxArguments (Fin n) arity Gamma types) :
    (argumentAt Gamma index (argumentsCode args)).bind
        (fun child => focusCode path child.1 child.2.1 child.2.2) =
      (argumentFocusWith (fun q => focus path q) index args).map argumentFocusValue := by
  induction index generalizing types with
  | zero =>
    cases args with
    | nil => simp [argumentAt, argumentsCode, argumentEntries, argumentFocusWith]
    | cons q rest =>
      have h := hvisit _ q
      unfold termFocusValue at h
      simpa only [argumentAt_zero, Option.bind_some, argumentFocusWith,
        Option.map_map, Function.comp_def, argumentFocusValue] using h
  | succ index ih =>
    cases args with
    | nil => simp [argumentAt, argumentsCode, argumentEntries, argumentFocusWith]
    | cons q rest =>
      have h := ih rest
      unfold argumentFocusValue at h
      simpa only [argumentAt_succ, argumentFocusWith, Option.map_map,
        Function.comp_def, argumentFocusValue] using h

theorem argumentReplacementCalibration {n : Nat} {arity : Fin n → Nat}
    (path : List Position)
    (hvisit : ∀ (Gamma : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau)
      (f : TermFocus n arity Gamma tau)
      (replacement : AuxTerm (Fin n) arity f.holeGamma f.holeType),
      focus path q = some f →
        replaceCode path Gamma tau (termCode q) (termCode replacement) =
          some (termCode (plug f.context replacement)))
    {Gamma types : List Ty} (index : Nat) (args : AuxArguments (Fin n) arity Gamma types) :
    ∀ (f : ArgumentFocus n arity Gamma types)
      (replacement : AuxTerm (Fin n) arity f.holeGamma f.holeType),
      argumentFocusWith (fun q => focus path q) index args = some f →
        replaceArgumentFocus path Gamma index (argumentsCode args) (termCode replacement) =
          some (argumentsCode (plugArguments f.context replacement)) := by
  induction index generalizing types with
  | zero =>
    cases args with
    | nil => intro f replacement h; simp [argumentFocusWith] at h
    | cons q rest =>
      intro f replacement h
      simp only [argumentFocusWith, Option.map_eq_some_iff] at h
      obtain ⟨child, hchild, rfl⟩ := h
      rw [replaceArgumentFocus_zero, hvisit _ _ q child replacement hchild]
      rfl
  | succ index ih =>
    cases args with
    | nil => intro f replacement h; simp [argumentFocusWith] at h
    | cons q rest =>
      intro f replacement h
      simp only [argumentFocusWith, Option.map_eq_some_iff] at h
      obtain ⟨child, hchild, rfl⟩ := h
      rw [replaceArgumentFocus_succ, ih rest child replacement hchild]
      rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeSupportProof

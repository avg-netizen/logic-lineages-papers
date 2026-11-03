module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeFieldsProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedCodeView
open NumberedHeadCodecPrimrecSupportProof NumberedSyntaxBoundsPrimrecSupportProof

/-- Constructor fields inspected by the exchange checker, with unused fields defaulted. -/
abbrev Fields (n : Nat) :=
  Nat × Ty × HeadCode (Fin n) × Nat × List Ty × Code (Fin n) × Code (Fin n)

def fields {n : Nat} : Code (Fin n) → Fields n
  | .var _ => (0, .ground, .zero, 0, [], .var 0, .var 0)
  | .lam sigma body => (1, sigma, .zero, 0, [], body, .var 0)
  | .app sigma q a => (2, sigma, .zero, 0, [], q, a)
  | .bottom tau => (3, tau, .zero, 0, [], .var 0, .var 0)
  | .ordinary head base => (4, .ground, head, 0, [], base, .var 0)
  | .numbered k head tau base types extras => (5, tau, head, k, types, base, extras)
  | .argumentsNil => (6, .ground, .zero, 0, [], .var 0, .var 0)
  | .argumentsCons tau q rest => (7, tau, .zero, 0, [], q, rest)

def viewFields (n : Nat) : CodeView n → Fields n :=
  Sum.elim (fun _ : Nat => (0, .ground, .zero, 0, [], .var 0, .var 0))
    (Sum.elim (fun p : Ty × Code (Fin n) => (1, p.1, .zero, 0, [], p.2, .var 0))
      (Sum.elim (fun p : Ty × Code (Fin n) × Code (Fin n) =>
        (2, p.1, .zero, 0, [], p.2.1, p.2.2))
        (Sum.elim (fun tau : Ty => (3, tau, .zero, 0, [], .var 0, .var 0))
          (Sum.elim (fun p : HeadCode (Fin n) × Code (Fin n) =>
            (4, .ground, p.1, 0, [], p.2, .var 0))
            (Sum.elim
              (fun p : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) =>
                (5, p.2.2.1, p.2.1, p.1, p.2.2.2.2.1, p.2.2.2.1, p.2.2.2.2.2))
              (Sum.elim (fun _ : Unit => (6, .ground, .zero, 0, [], .var 0, .var 0))
                (fun p : Ty × Code (Fin n) × Code (Fin n) =>
                  (7, p.1, .zero, 0, [], p.2.1, p.2.2))))))))

theorem viewFieldsPrimitive (n : Nat) : Primrec (viewFields n) := by
  have hvar : Primrec (fun _ => (0, .ground, .zero, 0, [], .var 0, .var 0) : Nat → Fields n) :=
    (Primrec.const (0)).pair ((Primrec.const (Ty.ground)).pair ((Primrec.const (HeadCode.zero : HeadCode (Fin n))).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair ((Primrec.const (Code.var 0 : Code (Fin n))).pair (Primrec.const (Code.var 0 : Code (Fin n))))))))
  have hlam : Primrec (fun p => (1, p.1, .zero, 0, [], p.2, .var 0) : Ty × Code (Fin n) → Fields n) :=
    (Primrec.const (1)).pair (((Primrec.fst.comp Primrec.id)).pair ((Primrec.const (HeadCode.zero : HeadCode (Fin n))).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair (((Primrec.snd.comp Primrec.id)).pair (Primrec.const (Code.var 0 : Code (Fin n))))))))
  have happ : Primrec (fun p => (2, p.1, .zero, 0, [], p.2.1, p.2.2) : Ty × Code (Fin n) × Code (Fin n) → Fields n) :=
    (Primrec.const (2)).pair (((Primrec.fst.comp Primrec.id)).pair ((Primrec.const (HeadCode.zero : HeadCode (Fin n))).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair (((Primrec.fst.comp (Primrec.snd.comp Primrec.id))).pair ((Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))))
  have hbottom : Primrec (fun tau => (3, tau, .zero, 0, [], .var 0, .var 0) : Ty → Fields n) :=
    (Primrec.const (3)).pair ((Primrec.id).pair ((Primrec.const (HeadCode.zero : HeadCode (Fin n))).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair ((Primrec.const (Code.var 0 : Code (Fin n))).pair (Primrec.const (Code.var 0 : Code (Fin n))))))))
  have hordinary : Primrec (fun p => (4, .ground, p.1, 0, [], p.2, .var 0) : HeadCode (Fin n) × Code (Fin n) → Fields n) :=
    (Primrec.const (4)).pair ((Primrec.const (Ty.ground)).pair (((Primrec.fst.comp Primrec.id)).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair (((Primrec.snd.comp Primrec.id)).pair (Primrec.const (Code.var 0 : Code (Fin n))))))))
  have hnumbered : Primrec (fun p => (5, p.2.2.1, p.2.1, p.1, p.2.2.2.2.1, p.2.2.2.1, p.2.2.2.2.2) : Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n) → Fields n) :=
    (Primrec.const (5)).pair (((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))).pair (((Primrec.fst.comp (Primrec.snd.comp Primrec.id))).pair (((Primrec.fst.comp Primrec.id)).pair (((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))).pair (((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))).pair ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))))))
  have hnil : Primrec (fun _ => (6, .ground, .zero, 0, [], .var 0, .var 0) : Unit → Fields n) :=
    (Primrec.const (6)).pair ((Primrec.const (Ty.ground)).pair ((Primrec.const (HeadCode.zero : HeadCode (Fin n))).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair ((Primrec.const (Code.var 0 : Code (Fin n))).pair (Primrec.const (Code.var 0 : Code (Fin n))))))))
  have hcons : Primrec (fun p => (7, p.1, .zero, 0, [], p.2.1, p.2.2) : Ty × Code (Fin n) × Code (Fin n) → Fields n) :=
    (Primrec.const (7)).pair (((Primrec.fst.comp Primrec.id)).pair ((Primrec.const (HeadCode.zero : HeadCode (Fin n))).pair ((Primrec.const (0)).pair ((Primrec.const ([] : List Ty)).pair (((Primrec.fst.comp (Primrec.snd.comp Primrec.id))).pair ((Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))))
  exact sumElim hvar (sumElim hlam (sumElim happ (sumElim hbottom (sumElim hordinary (sumElim hnumbered (sumElim hnil (hcons)))))))

theorem fieldsPrimitive (n : Nat) : Primrec (@fields n) :=
  ((viewFieldsPrimitive n).comp (NumberedCodeViewProof.viewPrimitive n)).of_eq
    (by intro code; cases code <;> rfl)

def dependencies {Symbol : Type} (p : Code Symbol × Code Symbol) :
    List (Code Symbol × Code Symbol) :=
  NumberedCodeEnumerationPrimrecSupportProof.cross (children p.1) (children p.2)

theorem dependenciesPrimitive (n : Nat) : Primrec (@dependencies (Fin n)) :=
  NumberedCodeEnumerationPrimrecSupportProof.crossPrimitive.comp
    ((childrenPrimitive n).comp Primrec.fst) ((childrenPrimitive n).comp Primrec.snd)

theorem dependenciesDecrease (n : Nat) (p child : Code (Fin n) × Code (Fin n))
    (h : child ∈ dependencies p) : codeNumber child.1 < codeNumber p.1 := by
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp h
  obtain ⟨b, _, hab⟩ := List.mem_map.mp hb
  cases hab
  exact childrenDecrease n p.1 a ha

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeFieldsProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeFieldsProof

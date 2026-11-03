module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open ProtectedPrefix

def LiteralMask : Prop := ∀ (pre Gamma : List Ty),
  (∀ {tau : Ty} (v : Variable pre tau),mask pre Gamma (boundVariable Gamma v)=true) ∧
  (∀ {tau : Ty} (v : Variable Gamma tau),mask pre Gamma (freeRename pre Gamma v)=false)

def OldNameLift : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta pre : List Ty)
    (s : MarkedSubstitution Symbol arity Gamma Delta) (tau : Ty) (v : Variable Gamma tau),
  liftFree pre s (freeRename pre Gamma v)=renameTerm (s v) (freeRename pre Delta)

def ClosingOldName : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Delta pre : List Ty)
    (consumed : Arguments Symbol arity Delta pre) (tau : Ty) (v : Variable Delta tau),
  closePrefix consumed (freeRename pre Delta v)=MarkedTerm.var v

def RaisedSourceClosing : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Delta pre : List Ty)
    (consumed : Arguments Symbol arity Delta pre) (tau : Ty) (q : MarkedTerm Symbol arity Delta tau),
  substituteTerm (renameTerm q (freeRename pre Delta)) (closePrefix consumed)=q

def RaisedSourceApplication : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Delta pre : List Ty)
    (consumed : Arguments Symbol arity Delta pre) (sigma tau : Ty)
    (types : List Ty) (q : MarkedTerm Symbol arity Delta sigma)
    (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau),
  applyOriginalWith (renameTerm q (freeRename pre Delta)) (closePrefix consumed) args h=
    applyOriginalWith q (fun v => .var v) args h

def OriginalVariableBlocked : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Delta pre : List Ty)
    (consumed : Arguments Symbol arity Delta pre) (sigma tau : Ty) (v : Variable pre sigma)
    (types : List Ty) (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau),
  types≠[] → applyOriginalWith (.var (boundVariable Delta v)) (closePrefix consumed) args h=none

def LiteralBinderStep : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta pre : List Ty)
    (s : MarkedSubstitution Symbol arity Gamma Delta) (consumed : Arguments Symbol arity Delta pre)
    (sigma tau : Ty) (rest : List Ty)
    (body : MarkedTerm Symbol arity (sigma::(pre++Gamma)) (arrows rest tau))
    (a : MarkedTerm Symbol arity Delta sigma) (args : Arguments Symbol arity Delta rest),
  applyFrame (.lam body) s consumed (.cons a args) rfl=
    applyFrame body s (.cons a consumed) args rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixTargets

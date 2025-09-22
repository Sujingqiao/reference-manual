```lean -show
section
open Lean (Syntax MacroM)
```
```lean
syntax &"notFive" term:arg : term
open Lean in
macro_rules
  | `(term|notFive 5) =>
    Macro.throwError "'5' is not allowed here"
  | `(term|notFive $e) =>
    pure e
```
```lean (name := notFiveAdd)
#eval notFive (2 + 3)
```
```leanOutput notFiveAdd
5
```
```leanOutput notFiveAdd
5
```
```lean (name := notFiveFive) +error
#eval notFive 5
```
```leanOutput notFiveFive
'5' is not allowed here
```
```leanOutput notFiveFive
'5' is not allowed here
```
```lean -keep -show
-- Test claim in preceding paragraph that it's OK for macros to give up prior to elab
syntax "doubled " term:arg : term

macro_rules
  | `(term|doubled $n:num) => `($n * 2)
  | `(term|doubled $_) => Lean.Macro.throwUnsupported

/-- info: 10 -/
#check_msgs in
#eval doubled 5

/--
error: elaboration function for `termDoubled_` has not been implemented
  doubled (5 + 2)
-/
#check_msgs in
#eval doubled (5 + 2)

elab_rules : term
  | `(term|doubled $e:term) => Lean.Elab.Term.elabTerm e none

/-- info: 7 -/
#check_msgs in
#eval doubled (5 + 2)
```
```lean -show
open Lean
```
```lean +error (name := cmdQuot)
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1 $cmd2)
```
```leanOutput cmdQuot
Application type mismatch: The argument
  cmd1
has type
  TSyntax `command
but is expected to have type
  TSyntax `term
in the application
  cmd1.raw
```
```leanOutput cmdQuot
Application type mismatch: The argument
  cmd1
has type
  TSyntax `command
but is expected to have type
  TSyntax `term
in the application
  cmd1.raw
```
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1:command $cmd2:command)
```
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1 $cmd2 #eval "hello!")
```
```lean -show
-- There is no way to extract parser priorities (they're only saved in the Pratt tables next to
-- compiled Parser code), so this test of priorities checks the observable relative priorities of the
-- quote parsers.

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `term)
-/
#check_msgs in
#check (`($(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node2 info `Lean.Parser.Term.app { raw := Syntax.missing }.raw
            (Syntax.node1 info `null { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `term)
-/
#check_msgs in
#check (`($(⟨.missing⟩) $(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node2 info `null { raw := Syntax.missing }.raw
            { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `command)
-/
#check_msgs in
#check (`($(⟨.missing⟩):command $(⟨.missing⟩)) : MacroM _)

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `tactic)
-/
#check_msgs in
#check (`(tactic| $(⟨.missing⟩):tactic) : MacroM _)

/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node1 info `Lean.Parser.Tactic.seq1
            (Syntax.node3 info `null { raw := Syntax.missing }.raw (Syntax.atom info ";")
              { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `tactic.seq)
-/
#check_msgs in
#check (`(tactic|
          $(⟨.missing⟩):tactic; $(⟨.missing⟩)) : MacroM _)
```
```lean -show
section M
variable {m : Type → Type}
open Lean (MonadRef MonadQuotation)
open Lean.Elab.Term (TermElabM)
open Lean.Elab.Command (CommandElabM)
open Lean.Elab.Tactic (TacticM)
```
```lean -show
end M
```
```lean -show
-- Verify claim about monads above
open Lean in
example [Monad m] [MonadQuotation m] : m Syntax := `(term|2 + 2)
```
```lean -show
section
open Lean
example (e : Term) : MacroM Syntax := `(term| $e)

example (e : Term) : MacroM Syntax := `(term| $(e))

--example (e : Term) : MacroM Syntax := `(term| $ (e))

end
```
```lean -show
section
open Lean (TSyntax SyntaxNodeKinds)
variable {c : SyntaxNodeKinds}
```
```lean
open Lean in
example [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `($x + $(quote (n + 2)))
```
```lean -show
open Lean
```
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```
```lean (name := ex1)
def ex1 (e) := show m _ from `(2 + $e)
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `term) : m (TSyntax `term)
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `term) : m (TSyntax `term)
```
```lean (name := ex2)
def ex2 (e) := show m _ from `(2 + $e:num)
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `num) : m (TSyntax `term)
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `num) : m (TSyntax `term)
```
```leanOutput ex2err1
<example>:1:34-1:36: unexpected token '$'; expected '`(tactic|' or no space before spliced term
```
```leanOutput ex2err1
<example>:1:34-1:36: unexpected token '$'; expected '`(tactic|' or no space before spliced term
```
```leanOutput ex2err2
<example>:1:37-1:39: unexpected token ':'; expected ')'
```
```leanOutput ex2err2
<example>:1:37-1:39: unexpected token ':'; expected ')'
```
```lean -show
end
```
```lean (name := expansion)
open Lean in
def f [Monad m] [MonadQuotation m]
    (x : Term) (n : Nat) : m Syntax :=
  `(fun k => $x + $(quote (n + 2)) + k)
#print f
```
```leanOutput expansion
def f : {m : Type → Type} → [Monad m] → [Lean.MonadQuotation m] → Lean.Term → Nat → m Syntax :=
fun {m} [Monad m] [Lean.MonadQuotation m] x n => do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let quotCtx ← Lean.MonadQuotation.getContext
  pure
      {
          raw :=
            Syntax.node2 info `Lean.Parser.Term.fun (Syntax.atom info "fun")
              (Syntax.node4 info `Lean.Parser.Term.basicFun
                (Syntax.node1 info `null (Syntax.ident info "k".toSubstring' (Lean.addMacroScope quotCtx `k scp) []))
                (Syntax.node info `null #[]) (Syntax.atom info "=>")
                (Syntax.node3 info `«term_+_»
                  (Syntax.node3 info `«term_+_» x.raw (Syntax.atom info "+") (Lean.quote `term (n + 2)).raw)
                  (Syntax.atom info "+")
                  (Syntax.ident info "k".toSubstring' (Lean.addMacroScope quotCtx `k scp) []))) }.raw
```
```leanOutput expansion
def f : {m : Type → Type} → [Monad m] → [Lean.MonadQuotation m] → Lean.Term → Nat → m Syntax :=
fun {m} [Monad m] [Lean.MonadQuotation m] x n => do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let quotCtx ← Lean.MonadQuotation.getContext
  pure
      {
          raw :=
            Syntax.node2 info `Lean.Parser.Term.fun (Syntax.atom info "fun")
              (Syntax.node4 info `Lean.Parser.Term.basicFun
                (Syntax.node1 info `null (Syntax.ident info "k".toSubstring' (Lean.addMacroScope quotCtx `k scp) []))
                (Syntax.node info `null #[]) (Syntax.atom info "=>")
                (Syntax.node3 info `«term_+_»
                  (Syntax.node3 info `«term_+_» x.raw (Syntax.atom info "+") (Lean.quote `term (n + 2)).raw)
                  (Syntax.atom info "+")
                  (Syntax.ident info "k".toSubstring' (Lean.addMacroScope quotCtx `k scp) []))) }.raw
```
```lean -show
section
open Lean (Term)
open Lean.Quote
variable {x : Term} {n : Nat}
```
```lean -show
end
```
```lean -show
open Lean
open Lean.Elab.Command (CommandElabM)
```
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```
```lean (name := ex1)
def ex1 (xs) := show m _ from `(#[$xs,*])
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Syntax.TSepArray `term ",") : m (TSyntax `term)
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Syntax.TSepArray `term ",") : m (TSyntax `term)
```
```lean (name := ex2)
def ex2 (xs : Array (TSyntax `term)) :=
  show m _ from `(#[$xs,*])
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```
```lean (name := ex3)
def ex3 (size : Nat) := show CommandElabM _ from do
  let mut nums : Array Nat := #[]
  for i in [0:size] do
    nums := nums.push i
  let stx ← `(#[$(nums.map (Syntax.mkNumLit ∘ toString)):num,*])
  -- Using logInfo here causes the syntax to be rendered via
  -- the pretty printer.
  logInfo stx

#eval ex3 4
```
```leanOutput ex3
#[0, 1, 2, 3]
```
```leanOutput ex3
#[0, 1, 2, 3]
```
```lean
syntax "⟦" sepBy1(num, " — ") "⟧": term
syntax "⟦" sepBy1(num, " ** ") "⟧": term
```
```lean
macro_rules
  | `(⟦$n:num—*⟧) => `(⟦$n***⟧)
  | `(⟦$n:num***⟧) => `([$n,*])
```
```lean (name := nonComma)
#eval ⟦1 — 2 — 3⟧
```
```leanOutput nonComma
[1, 2, 3]
```
```leanOutput nonComma
[1, 2, 3]
```
```lean -show
open Lean
```
```lean
syntax "⟨| " (term)? " |⟩": term
```
```lean
def mkStx [Monad m] [MonadQuotation m]
    (e : Option Term) : m Term :=
  `(⟨| $(e)? |⟩)
```
```lean (name := checkMkStx)
#check mkStx
```
```leanOutput checkMkStx
mkStx {m : Type → Type} [Monad m] [MonadQuotation m] (e : Option Term) : m Term
```
```leanOutput checkMkStx
mkStx {m : Type → Type} [Monad m] [MonadQuotation m] (e : Option Term) : m Term
```
```lean (name := someMkStx)
#eval do logInfo (← mkStx (some (quote 5)))
```
```leanOutput someMkStx
⟨| 5 |⟩
```
```leanOutput someMkStx
⟨| 5 |⟩
```
```lean (name := noneMkStx)
#eval do logInfo (← mkStx none)
```
```leanOutput noneMkStx
⟨| |⟩
```
```leanOutput noneMkStx
⟨| |⟩
```
```lean -show
section
open Lean Syntax
variable {k k' : SyntaxNodeKinds} {sep : String} [Coe (TSyntax k) (TSyntax k')]
-- Demonstrate the coercions between different kinds of repeated syntax

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k' sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (Array (TSyntax k)) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSepArray k sep) (TSyntaxArray k)

end
```
```lean
syntax (name := idiom) "⟦" (term:arg)+ "⟧" : term

macro_rules
  | `(⟦$f $args*⟧) => do
    let mut out ← `(pure $f)
    for arg in args do
      out ← `($out <*> $arg)
    return out
```
```lean
def addFirstThird [Add α] (xs : List α) : Option α :=
  ⟦Add.add xs[0]? xs[2]?⟧
```
```lean (name := idiom1)
#eval addFirstThird (α := Nat) []
```
```leanOutput idiom1
none
```
```leanOutput idiom1
none
```
```lean (name := idiom2)
#eval addFirstThird [1]
```
```leanOutput idiom2
none
```
```leanOutput idiom2
none
```
```lean (name := idiom3)
#eval addFirstThird [1,2,3,4]
```
```leanOutput idiom3
some 4
```
```leanOutput idiom3
some 4
```
```lean
namespace ConfusingNumbers
```
```lean
scoped macro_rules
  | `($n:num) => do
    if n.getNat % 2 = 0 then Lean.Macro.throwUnsupported
    let n' := (n.getNat * 2)
    `($(Syntax.mkNumLit (info := n.raw.getHeadInfo) (toString n')))
```
```lean
end ConfusingNumbers
```
```lean (name := nums1)
#eval (3, 4)
```
```leanOutput nums1
(3, 4)
```
```leanOutput nums1
(3, 4)
```
```lean (name := nums2)
open ConfusingNumbers

#eval (3, 4)
```
```leanOutput nums2
(6, 4)
```
```leanOutput nums2
(6, 4)
```
```lean -show
open Lean.Macro
```
```lean
syntax (name := arbitrary!) "arbitrary! " term:arg : term
```
```lean
macro_rules
  | `(arbitrary! ()) => `(())
  | `(arbitrary! Nat) => `(42)
  | `(arbitrary! ($t1 × $t2)) => `((arbitrary! $t1, arbitrary! $t2))
  | `(arbitrary! Nat) => `(0)
```
```lean
macro_rules
  | `(arbitrary! Empty) => throwUnsupported
```
```lean (name := arb1)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb1
(42, 42)
```
```leanOutput arb1
(42, 42)
```
```lean
macro_rules
  | `(arbitrary! ()) =>
    `(())
macro_rules
  | `(arbitrary! Nat) =>
    `(42)
macro_rules
  | `(arbitrary! ($t1 × $t2)) =>
    `((arbitrary! $t1, arbitrary! $t2))
macro_rules
  | `(arbitrary! Nat) =>
    `(0)
macro_rules
  | `(arbitrary! Empty) =>
    throwUnsupported
```
```lean (name := arb2)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb2
(0, 0)
```
```leanOutput arb2
(0, 0)
```
```lean
macro_rules
  | `(arbitrary! (List Nat)) => throwUnsupported
  | `(arbitrary! (List $_)) => `([])

macro_rules
  | `(arbitrary! (Array Nat)) => `(#[42])
macro_rules
  | `(arbitrary! (Array $_)) => throwUnsupported
```
```lean (name := arb3) +error
#eval arbitrary! (List Nat)
```
```leanOutput arb3
elaboration function for `arbitrary!` has not been implemented
  arbitrary! (List Nat)
```
```leanOutput arb3
elaboration function for `arbitrary!` has not been implemented
  arbitrary! (List Nat)
```
```lean (name := arb4)
#eval arbitrary! (Array Nat)
```
```leanOutput arb4
#[42]
```
```leanOutput arb4
#[42]
```
```lean -show
section
open Lean
```
```lean -show -keep
-- Check the typing rules
open Lean Elab Term Macro Meta

elab "dbg_type " e:term ";" body:term : term => do
  let e' ← elabTerm e none
  let t ← inferType e'
  logInfoAt e t
  elabTerm body none

/--
info: TSyntax `str
---
info: TSyntax Name.anonymous
---
info: Syntax.TSepArray `num ","
-/
#check_msgs in
macro "gah!" thing:str other:(str <|> num) arg:num,* : term => do
  dbg_type thing; pure ()
  dbg_type other; pure ()
  dbg_type arg; pure ()
  return quote s!"{thing.raw} ||| {other.raw} ||| {arg.getElems}"

/-- info: "(str \"\\\"one\\\"\") ||| (num \"44\") ||| #[(num \"2\"), (num \"3\")]" : String -/
#check_msgs in
#check gah! "one" 44 2,3

```
```lean -show
end
```
```lean -show
open Lean Macro
```
```lean
/-- Generate a list based on N syntactic copies of a term -/
syntax (name := rep) "[" num " !!! " term "]" : term

@[macro rep]
def expandRep : Macro
  | `([ $n:num !!! $e:term]) =>
    let e' := Array.mkArray n.getNat e
    `([$e',*])
  | _ =>
    throwUnsupported
```
```lean (name := attrEx1)
#eval [3 !!! "hello"]
```
```leanOutput attrEx1
["hello", "hello", "hello"]
```
```leanOutput attrEx1
["hello", "hello", "hello"]
```
```lean -show
open Lean.PrettyPrinter (Unexpander UnexpandM)
```
```lean
structure Solo where
  mk ::

syntax "‹" "›" : term

macro_rules
  | `(term|‹›) => ``(Solo.mk)
```
```lean
@[app_unexpander Solo.mk]
def unexpandSolo : Lean.PrettyPrinter.Unexpander
  | _ => `(‹›)
```
```lean
structure ListCursor (α) where
  before : List α
  after : List α
deriving Repr
```
```lean
def ListCursor.left : ListCursor α → Option (ListCursor α)
  | ⟨[], _⟩ => none
  | ⟨l :: ls, rs⟩ => some ⟨ls, l :: rs⟩

def ListCursor.right : ListCursor α → Option (ListCursor α)
  | ⟨_, []⟩ => none
  | ⟨ls, r :: rs⟩ => some ⟨r :: ls, rs⟩
```
```lean
def ListCursor.rewind : ListCursor α → ListCursor α
  | xs@⟨[], _⟩ => xs
  | ⟨l :: ls, rs⟩ => rewind ⟨ls, l :: rs⟩
termination_by xs => xs.before

def ListCursor.fastForward : ListCursor α → ListCursor α
  | xs@⟨_, []⟩ => xs
  | ⟨ls, r :: rs⟩ => fastForward ⟨r :: ls, rs⟩
termination_by xs => xs.after
```
```lean -show
def ListCursor.ofList (xs : List α) : ListCursor α where
  before := []
  after := xs

def ListCursor.toList : (xs : ListCursor α) → List α
  | ⟨[], rs⟩ => rs
  | ⟨l::ls, rs⟩ => toList ⟨ls, l :: rs⟩
termination_by xs => xs.before
```
```lean
syntax "[" term,* " 🚩 " term,* "]": term
macro_rules
  | `([$ls,* 🚩 $rs,*]) =>
    ``(ListCursor.mk [$[$((ls : Array Lean.Term).reverse)],*] [$rs,*])
```
```lean (name := flagNo)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagNo
{ before := [3, 2, 1], after := [4, 5] } : ListCursor Nat
```
```leanOutput flagNo
{ before := [3, 2, 1], after := [4, 5] } : ListCursor Nat
```
```lean
@[app_unexpander ListCursor.mk]
def unexpandListCursor : Lean.PrettyPrinter.Unexpander
  | `($_ [$ls,*] [$rs,*]) =>
    `([$((ls : Array Lean.Term).reverse),* 🚩 $(rs),*])
  | _ => throw ()
```
```lean (name := flagYes)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagYes
[1, 2, 3 🚩 4, 5] : ListCursor Nat
```
```leanOutput flagYes
[1, 2, 3 🚩 4, 5] : ListCursor Nat
```
```lean (name := flagYes2)
#reduce [1, 2, 3 🚩 4, 5].right
```
```leanOutput flagYes2
some [1, 2, 3, 4 🚩 5]
```
```leanOutput flagYes2
some [1, 2, 3, 4 🚩 5]
```
```lean (name := flagYes3)
#reduce [1, 2, 3 🚩 4, 5].left >>= (·.left)
```
```leanOutput flagYes3
some [1 🚩 2, 3, 4, 5]
```
```leanOutput flagYes3
some [1 🚩 2, 3, 4, 5]
```
```lean -show
open Lean.PrettyPrinter.Delaborator (DelabM Delab)
open Lean (Term)
```
```lean -show
open Lean.PrettyPrinter.Delaborator.SubExpr
``````lean -show
open Lean Elab Command
```
```lean
syntax "#count_constants " ident : command

elab_rules : command
  | `(#count_constants%$tok $x) => do
    let pattern := x.getId
    let env ← getEnv
    let mut count := 0
    for (y, _) in env.constants do
      if pattern.isSuffixOf y then
        count := count + 1
    logInfoAt tok m!"Found {count} instances of '{pattern}'"
```
```lean (name := run)
def interestingName := 55
def NS.interestingName := "Another one"

#count_constants interestingName
```
```leanOutput run
Found 2 instances of 'interestingName'
```
```leanOutput run
Found 2 instances of 'interestingName'
```
```lean -show
open Lean Elab Term
```
```lean
syntax (name := notType) "(" term  " !: " term ")" : term

@[term_elab notType]
def elabNotType : TermElab := fun stx _ => do
  let `(($tm:term !: $ty:term)) := stx
    | throwUnsupportedSyntax
  let unexpected ← elabType ty
  let e ← elabTerm tm none
  let eTy ← Meta.inferType e
  if (← Meta.isDefEq eTy unexpected) then
    throwErrorAt tm m!"Got unwanted type {eTy}"
  else pure e
```
```lean (name := notType) +error
#eval ([1, 2, 3] !: "not a type")
```
```leanOutput notType
type expected, got
  ("not a type" : String)
```
```leanOutput notType
type expected, got
  ("not a type" : String)
```
```lean (name := ok)
#eval ([1, 2, 3] !: String)
```
```leanOutput ok
[1, 2, 3]
```
```leanOutput ok
[1, 2, 3]
```
```lean (name := nope) +error
#eval (5 !: Nat)
```
```leanOutput nope
Got unwanted type Nat
```
```leanOutput nope
Got unwanted type Nat
```
```lean (name := unif) +error
#eval (sorry !: String)
```
```leanOutput unif
Got unwanted type String
```
```leanOutput unif
Got unwanted type String
```
```lean
syntax "anything!" : term

elab_rules <= expected
  | `(anything!) => do
    let hyps ← getLocalHyps
    for h in hyps.reverse do
      let t ← Meta.inferType h
      if (← Meta.isDefEq t expected) then return h

    throwError m!"No assumption in {hyps} has type {expected}"
```
```lean (name := app)
#eval (fun (n : Nat) => 2 + anything!) 5
```
```leanOutput app
7
```
```leanOutput app
7
```
```lean (name := lets)
#eval
  let x := "x"
  let y := "y"
  "It was " ++ y
```
```leanOutput lets
"It was y"
```
```leanOutput lets
"It was y"
```
```lean (name := noFun) +error
#eval
  let x := Nat.zero
  let y := "hello"
  fun (f : Nat → Nat) =>
    (anything! : Int → Int)
```
```leanOutput noFun
No assumption in [x, y, f] has type Int → Int
```
```leanOutput noFun
No assumption in [x, y, f] has type Int → Int
```
```lean (name := poly) +error
#eval
  let x := 5
  let y := "hello"
  (anything! : Int → Int)
```
```leanOutput poly
failed to synthesize
  OfNat (Int → Int) 5
numerals are polymorphic in Lean, but the numeral `5` cannot be used in a context where the expected type is
  Int → Int
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput poly
failed to synthesize
  OfNat (Int → Int) 5
numerals are polymorphic in Lean, but the numeral `5` cannot be used in a context where the expected type is
  Int → Int
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
``````lean -keep -show

-- Test for default precedences for notations

/-- Parser max -/
notation "takesMax " e:max => e
/-- Parser lead -/
notation "takesLead " e:lead => e
/-- Parser min -/
notation "takesMin " e:min => e

/-- Take the first one -/
notation e1 " <# " e2 => e1

/-- Take the first one in brackets! -/
notation "<<<<<" e1 " <<# " e2 ">>>>>" => e1

elab "#parse_test " "[" e:term "]"  : command => do
  Lean.logInfoAt e (toString e)
  pure ()

-- Here, takesMax vs takesLead distinguishes the notations

/-- info: («term_<#_» (termTakesMax_ "takesMax" (num "1")) "<#" (num "2")) -/
#check_msgs in
#parse_test [ takesMax 1 <# 2 ]

/-- info: (termTakesLead_ "takesLead" («term_<#_» (num "1") "<#" (num "2"))) -/
#check_msgs in
#parse_test [ takesLead 1 <# 2 ]


-- Here, takesMax vs takesLead does not distinguish the notations because both have precedence `max`

/--
info: (termTakesMax_ "takesMax" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesMax <<<<< 1 <<# 2 >>>>> ]

/--
info: (termTakesLead_ "takesLead" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesLead <<<<< 1 <<# 2 >>>>> ]
```
```lean
notation (name := ignore) "ignore " _ign:arg e:arg => e
```
```lean (name := ignore)
#eval ignore (2 + "whatever") 5
```
```leanOutput ignore
5
```
```leanOutput ignore
5
```
```leanOutput ignore'
<example>:1:17-1:18: unexpected token ')'; expected term
```
```leanOutput ignore'
<example>:1:17-1:18: unexpected token ')'; expected term
```
```lean
notation (name := dup) "dup!" t:arg => (t, t)
```
```lean
def e : Nat × Int := dup! (2 + 2)
```
```lean (name := dup)
#print e
```
```leanOutput dup
def e : Nat × Int :=
(2 + 2, 2 + 2)
```
```leanOutput dup
def e : Nat × Int :=
(2 + 2, 2 + 2)
``````leanOutput eqs
  <example>:1:10-1:11: expected end of input
  ```
```leanOutput eqs
  <example>:1:10-1:11: expected end of input
  ```
```lean -show
axiom A : Prop
axiom B : Prop
example : (¬A ∧ B = (¬A) ∧ B) = (¬A ∧ ((B = ¬A) ∧ B)) := rfl
example : (¬A ∧ B) = ((¬A) ∧ B) := rfl
```
```lean
infix:90 " ⤴ " => Option.getD
```
```lean
infix:90 (name := getDOp) " ⤴ " => Option.getD
```
```lean
@[inherit_doc]
infix:90 " ⤴ " => Option.getD
```
```lean
infix:65  " + " => Or
```
```lean (name := trueOrFalse1)
#check True + False
```
```leanOutput trueOrFalse1
True + False : Prop
```
```leanOutput trueOrFalse1
True + False : Prop
```
```lean (name := twoPlusTwo1)
#check 2 + 2
```
```leanOutput twoPlusTwo1
2 + 2 : Nat
```
```leanOutput twoPlusTwo1
2 + 2 : Nat
```
```lean +error (name := trueOrFalseOrTrue1)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue1
failed to synthesize
  HAdd Prop Prop ?m.38

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput trueOrFalseOrTrue1
failed to synthesize
  HAdd Prop Prop ?m.38

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
infix:65 (priority := high)  " + " => Or
```
```lean (name := trueOrFalse2)
#check True + False
```
```leanOutput trueOrFalse2
True + False : Prop
```
```leanOutput trueOrFalse2
True + False : Prop
```
```lean (name := twoPlusTwo2) +error
#check 2 + 2
```
```leanOutput twoPlusTwo2
failed to synthesize
  OfNat Prop 2
numerals are polymorphic in Lean, but the numeral `2` cannot be used in a context where the expected type is
  Prop
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput twoPlusTwo2
failed to synthesize
  OfNat Prop 2
numerals are polymorphic in Lean, but the numeral `2` cannot be used in a context where the expected type is
  Prop
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean +error (name := trueOrFalseOrTrue2)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue2
failed to synthesize
  HAdd Prop Prop ?m.20

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput trueOrFalseOrTrue2
failed to synthesize
  HAdd Prop Prop ?m.20

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean -show
-- Test claim about internal whitespace in preceding paragraph
/-- error: invalid atom -/
#check_msgs in
infix:99 " <<<< >>>> " => Nat.add


--- Test further claims about allowed atoms
/-- error: invalid atom -/
#check_msgs in
infix:9 (name := bogus) "" => Nat.mul


/-- error: invalid atom -/
#check_msgs in
infix:9 (name := alsobogus) " ` " => Nat.mul

-- this one's OK
#check_msgs in
infix:9 (name := nonbogus) " `` " => Nat.mul

/-- error: invalid atom -/
#check_msgs in
infix:9 (name := bogus) "`a" => Nat.mul

```
```lean -show -keep
-- Double-check claims about operators above
prefix:max "blah" => Nat.add
#check (blah 5)
```
```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none
```
```lean
postfix:90 "‽" => perhapsFactorial
``````lean -show
  variable {α : Type u}
  variable {x : α}
  ```
```lean -show -keep
-- Verify claims about atoms and nodes
open Lean in
partial def noInfo : Syntax → Syntax
  | .node _ k children => .node .none k (children.map noInfo)
  | .ident _ s x pre => .ident .none s x pre
  | .atom _ s => .atom .none s
  | .missing => .missing
/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "0xabc123"]
-/
#check_msgs in
#eval noInfo <$> `(term|0xabc123)

/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"ab\\tc\""]
-/
#check_msgs in
#eval noInfo <$> `(term|"ab\tc")
```
```lean -show
section Inspecting
open Lean
```
```lean
partial def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing
```
```lean (name := reprStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (repr (removeSourceInfo stx.raw))
```
```leanOutput reprStx1
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `«term_+_»
  #[Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "2"],
    Lean.Syntax.atom (Lean.SourceInfo.none) "+", Lean.Syntax.missing]
```
```leanOutput reprStx1
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `«term_+_»
  #[Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "2"],
    Lean.Syntax.atom (Lean.SourceInfo.none) "+", Lean.Syntax.missing]
```
```lean (name := reprStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (repr (removeSourceInfo stx.raw))
```
```leanOutput reprStx2
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Term.app
  #[Lean.Syntax.ident
      (Lean.SourceInfo.none)
      "List.length".toSubstring
      (Lean.Name.mkNum `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg 2)
      [Lean.Syntax.Preresolved.decl `List.length [], Lean.Syntax.Preresolved.namespace `List.length],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `null
      #[Lean.Syntax.node
          (Lean.SourceInfo.none)
          `«term[_]»
          #[Lean.Syntax.atom (Lean.SourceInfo.none) "[",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Rose\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Daffodil\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Lily\""]],
            Lean.Syntax.atom (Lean.SourceInfo.none) "]"]]]
```
```leanOutput reprStx2
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Term.app
  #[Lean.Syntax.ident
      (Lean.SourceInfo.none)
      "List.length".toSubstring
      (Lean.Name.mkNum `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg 2)
      [Lean.Syntax.Preresolved.decl `List.length [], Lean.Syntax.Preresolved.namespace `List.length],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `null
      #[Lean.Syntax.node
          (Lean.SourceInfo.none)
          `«term[_]»
          #[Lean.Syntax.atom (Lean.SourceInfo.none) "[",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Rose\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Daffodil\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Lily\""]],
            Lean.Syntax.atom (Lean.SourceInfo.none) "]"]]]
```
```lean (name := toStringStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (toString stx)
```
```leanOutput toStringStx1
(«term_+_» (num "2") "+" <missing>)
```
```leanOutput toStringStx1
(«term_+_» (num "2") "+" <missing>)
```
```lean (name := toStringStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (toString stx)
```
```leanOutput toStringStx2
(Term.app
 `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg.2
 [(«term[_]» "[" [(str "\"Rose\"") "," (str "\"Daffodil\"") "," (str "\"Lily\"")] "]")])
```
```leanOutput toStringStx2
(Term.app
 `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg.2
 [(«term[_]» "[" [(str "\"Rose\"") "," (str "\"Daffodil\"") "," (str "\"Lily\"")] "]")])
```
```lean -show
open Lean Elab Command
```
```lean
def getPPContext : CommandElabM PPContext := do
  return {
    env := (← getEnv),
    opts := (← getOptions),
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
```
```lean (name := ppStx1)
#eval show CommandElabM Unit from do
  let stx ← `(2 + 5)
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx1
2 + 5
```
```leanOutput ppStx1
2 + 5
```
```lean (name := ppStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx2
List.length✝ ["Rose", "Daffodil", "Lily"]
```
```leanOutput ppStx2
List.length✝ ["Rose", "Daffodil", "Lily"]
```
```lean (name := ppStx3)
#eval do
  let flowers := #["Rose", "Daffodil", "Lily"]
  let manyFlowers := flowers ++ flowers ++ flowers
  let stx ← `(List.length [$(manyFlowers.map (quote (k := `term))),*])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo (fmt.pretty (width := 40))
```
```leanOutput ppStx3
List.length✝
  ["Rose", "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily"]
```
```leanOutput ppStx3
List.length✝
  ["Rose", "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily"]
```
```lean -show
end Inspecting
```
```lean -show
/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
open Lean in
#synth CoeHTCT (TSyntax `str) (TSyntax `term)
```
```lean -show
-- verify preceding para
/-- error: unknown category `nuhUh` -/
#check_msgs in
syntax "blah" : nuhUh
```
```lean
declare_syntax_cat balanced
```
```lean
syntax "(" ")" : balanced
syntax "[" "]" : balanced
syntax "(" balanced ")" : balanced
syntax "[" balanced "]" : balanced
syntax balanced balanced : balanced
```
```lean
syntax (name := termBalanced) "balanced " balanced : term
```
```lean
/--
error: elaboration function for `termBalanced` has not been implemented
  balanced ()
-/
#guard_msgs in
example := balanced ()

/--
error: elaboration function for `termBalanced` has not been implemented
  balanced []
-/
#guard_msgs in
example := balanced []

/--
error: elaboration function for `termBalanced` has not been implemented
  balanced [[]()([])]
-/
#guard_msgs in
example := balanced [[] () ([])]
```
```leanOutput mismatch
<example>:1:25-1:26: unexpected token ']'; expected ')' or balanced
```
```leanOutput mismatch
<example>:1:25-1:26: unexpected token ']'; expected ')' or balanced
```
```lean
syntax "[[" term,*,? "]]" : term
```
```lean
macro_rules
  | `(term|[[$e:term,*]]) => `([$e,*])
```
```lean (name := evFunnyList)
#eval [["Dandelion", "Thistle",]]
```
```leanOutput evFunnyList
["Dandelion", "Thistle"]
```
```leanOutput evFunnyList
["Dandelion", "Thistle"]
```
```lean
syntax "note " ppLine withPosition((colEq "◦ " str ppLine)+) : term
```
```lean +error (name := noteEx1)
#check
  note
    ◦ "One"
    ◦ "Two"
```
```leanOutput noteEx1
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```
```leanOutput noteEx1
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```
```lean +error (name := noteEx15)
#check
  note
◦ "One"
◦ "Two"
```
```leanOutput noteEx15
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```
```leanOutput noteEx15
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```
```leanOutput noteEx2
<example>:4:3-4:4: expected end of input
```
```leanOutput noteEx2
<example>:4:3-4:4: expected end of input
```
```leanOutput noteEx2
<example>:4:5-4:6: expected end of input
```
```leanOutput noteEx2
<example>:4:5-4:6: expected end of input
```
```lean (name := localOverGlobal)
def x := "global"

#eval
  let x := "local"
  x
```
```leanOutput localOverGlobal
"local"
```
```leanOutput localOverGlobal
"local"
```
```lean (name := innermostLocal)
#eval
  let x := "outer"
  let x := "inner"
  x
```
```leanOutput innermostLocal
"inner"
```
```leanOutput innermostLocal
"inner"
```
```lean (name := NS)
namespace A
def x := "A.x"
namespace B
namespace C
def x := "A.B.C.x"
```
```lean (name := NSC)
#eval x
```
```leanOutput NSC
"A.B.C.x"
```
```leanOutput NSC
"A.B.C.x"
```
```lean (name := NSB)
end C
#eval x
```
```leanOutput NSB
"A.x"
```
```leanOutput NSB
"A.x"
```
```lean
structure A where
  y : String
deriving Repr

structure B where
  y : A
deriving Repr

def y : B := ⟨⟨"shorter"⟩⟩
def y.y : A := ⟨"longer"⟩
```
```lean (name := yyy)
#eval y.y.y
```
```leanOutput yyy
"longer"
```
```leanOutput yyy
"longer"
```
```lean
namespace A
def x := "A.x"
end A

namespace B
def x := "B.x"
namespace C
open A
#eval x
```
```lean (name := nestedVsOpen)
#eval x
```
```leanOutput nestedVsOpen
"B.x"
```
```leanOutput nestedVsOpen
"B.x"
```
```lean (name := ambi) +error
def A.x := "A.x"
def B.x := "B.x"
open A
open B
#eval x
```
```leanOutput ambi (whitespace := lax)
Ambiguous term
  x
Possible interpretations:
  B.x : String

  A.x : String
```
```leanOutput ambi (whitespace := lax)
Ambiguous term
  x
Possible interpretations:
  B.x : String

  A.x : String
```
```lean (name := ambiNo)
def C.x := "C.x"
def D.x := 3
open C
open D
#eval (x : String)
```
```leanOutput ambiNo
"C.x"
```
```leanOutput ambiNo
"C.x"
```
```lean (name := dotRep)
#eval show List Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
```leanOutput dotRep
[(), (), ()]
```
```lean (name := dotRep)
def MyList α := List α
#eval show MyList Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
```leanOutput dotRep
[(), (), ()]
```
```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```
```lean
example : f 2 = g 2 := rfl
```
```lean
example := f
```
```lean +error (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument `α`
  @g ?m.3
context:
⊢ Type
```
```leanOutput noAlpha
don't know how to synthesize implicit argument `α`
  @g ?m.3
context:
⊢ Type
```
```lean -show
-- Evidence of claims in prior paragraph
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```
```lean (name := funImplAdd)
#check (fun x => x : {α : Type} → α → α)
```
```leanOutput funImplAdd
fun {α} x => x : {α : Type} → α → α
```
```leanOutput funImplAdd
fun {α} x => x : {α : Type} → α → α
```
```lean (name := funImplThere)
#check (fun {α} x => x : {α : Type} → α → α)
```
```leanOutput funImplThere
fun {α} x => x : {α : Type} → α → α
```
```leanOutput funImplThere
fun {α} x => x : {α : Type} → α → α
```
```lean (name := funImplAnn)
#check (fun {α} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn
fun {α} x => x : {α : Type} → α → α
```
```leanOutput funImplAnn
fun {α} x => x : {α : Type} → α → α
```
```lean (name := funImplAnn2)
#check (fun {α : Type} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn2
fun {α} x => x : {α : Type} → α → α
```
```leanOutput funImplAnn2
fun {α} x => x : {α : Type} → α → α
```
```lean
def sum3 (x y z : Nat) : Nat := x + y + z
```
```lean (name := sum31)
#check sum3 1 3 8
```
```leanOutput sum31
sum3 1 3 8 : Nat
```
```leanOutput sum31
sum3 1 3 8 : Nat
```
```lean (name := sum32)
#check sum3 (x := 1) (y := 3) (z := 8)
```
```leanOutput sum32
sum3 1 3 8 : Nat
```
```leanOutput sum32
sum3 1 3 8 : Nat
```
```lean (name := sum33)
#check sum3 (y := 3) (z := 8) (x := 1)
```
```leanOutput sum33
sum3 1 3 8 : Nat
```
```leanOutput sum33
sum3 1 3 8 : Nat
```
```lean (name := sum34)
#check sum3 1 (z := 8) (y := 3)
```
```leanOutput sum34
sum3 1 3 8 : Nat
```
```leanOutput sum34
sum3 1 3 8 : Nat
```
```lean (name := sum342)
#check sum3 1 (x := 8) (y := 3)
```
```leanOutput sum342
sum3 8 3 1 : Nat
```
```leanOutput sum342
sum3 8 3 1 : Nat
```
```lean (name := sum35)
#check sum3 (z := 8)
```
```leanOutput sum35
fun x y => sum3 x y 8 : Nat → Nat → Nat
```
```leanOutput sum35
fun x y => sum3 x y 8 : Nat → Nat → Nat
```
```lean (name := sum36)
#check (sum3 (z := 8)) (y := 1)
```
```leanOutput sum36
fun x => (fun x y => sum3 x y 8) x 1 : Nat → Nat
```
```leanOutput sum36
fun x => (fun x y => sum3 x y 8) x 1 : Nat → Nat
```
```lean -show
-- This is not shown in the manual pending #6373
-- https://github.com/leanprover/lean4/issues/6373
-- When the issue is fixed, this code will stop working and the text can be updated.

/--
info: let x := 15;
fun x y => sum3 x y x : Nat → Nat → Nat
-/
#guard_msgs in
#check let x := 15; sum3 (z := x)
```
```lean -show
section
variable (name : Username)
```
```lean
def Username := String
```
```lean
def Username.validate (name : Username) : Except String Unit := do
  if " ".isPrefixOf name then
    throw "Unexpected leading whitespace"
  if name.any notOk then
    throw "Unexpected character"
  return ()
where
  notOk (c : Char) : Bool :=
    !c.isAlpha &&
    !c.isDigit &&
    !c ∈ ['_', ' ']

def root : Username := "root"
```
```lean +error (name := notString)
#eval "root".validate
```
```leanOutput notString
Invalid field `validate`: The environment does not contain `String.validate`
  "root"
has type
  String
```
```leanOutput notString
Invalid field `validate`: The environment does not contain `String.validate`
  "root"
has type
  String
```
```lean (name := isUsername)
#eval root.validate
```
```leanOutput isUsername
Except.ok ()
```
```leanOutput isUsername
Except.ok ()
```
```lean -show
end
```
```lean
def Nat.half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => n.half + 1
```
```lean (name := succ1)
#check Nat.half Nat.zero
```
```leanOutput succ1
Nat.zero.half : Nat
```
```leanOutput succ1
Nat.zero.half : Nat
```
```lean (name := succ2)
attribute [pp_nodot] Nat.half

#check Nat.half Nat.zero
```
```leanOutput succ2
Nat.half Nat.zero : Nat
```
```leanOutput succ2
Nat.half Nat.zero : Nat
```
```lean (name := rightPipe)
#eval "Hello!" |> String.toList |> List.reverse |> List.head!
```
```leanOutput rightPipe
'!'
```
```leanOutput rightPipe
'!'
```
```lean (name := lPipe)
#eval List.head! <| List.reverse <| String.toList <| "Hello!"
```
```leanOutput lPipe
'!'
```
```leanOutput lPipe
'!'
```
```lean -show
section
universe u
axiom T : Nat → Type u
variable {e : T 3} {arg : Char}
axiom T.f : {n : Nat} → Char → T n → String
```
```lean (name := arrPush) +error
#eval #[1, 2, 3] |> Array.push 4
```
```leanOutput arrPush
failed to synthesize
  OfNat (Array ?m.4) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Array ?m.4
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput arrPush
failed to synthesize
  OfNat (Array ?m.4) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Array ?m.4
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean (name := arrPush2)
#eval #[1, 2, 3] |>.push 4
```
```leanOutput arrPush2
#[1, 2, 3, 4]
```
```leanOutput arrPush2
#[1, 2, 3, 4]
```
```lean (name := arrPush3)
#eval #[1, 2, 3] |>.push 4 |>.reverse |>.push 0 |>.reverse
```
```leanOutput arrPush3
#[0, 1, 2, 3, 4]
```
```leanOutput arrPush3
#[0, 1, 2, 3, 4]
```
```lean -show
end
```
```lean -show
section
variable {n : Nat}
```
```lean -show
end
```
```lean
structure NatInterval where
  low : Nat
  high : Nat
  low_le_high : low ≤ high

instance : Add NatInterval where
  add
    | ⟨lo1, hi1, le1⟩, ⟨lo2, hi2, le2⟩ => ⟨lo1 + lo2, hi1 + hi2, by omega⟩
```
```lean
instance : OfNat NatInterval n where
  ofNat := ⟨n, n, by omega⟩
```
```lean (name := eval8Interval)
#eval (8 : NatInterval)
```
```leanOutput eval8Interval
{ low := 8, high := 8, low_le_high := _ }
```
```leanOutput eval8Interval
{ low := 8, high := 8, low_le_high := _ }
```
```lean (name := almostLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1]
```
```leanOutput almostLong
[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Nat
```
```leanOutput almostLong
[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Nat
```
```lean (name := indeedLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1]
```
```leanOutput indeedLong
let y :=
  let y :=
    let y := [1, 1, 1, 1, 1];
    1 :: 1 :: 1 :: 1 :: y;
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y :=
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y := 1 :: 1 :: 1 :: 1 :: y;
1 :: 1 :: 1 :: 1 :: y : List Nat
```
```leanOutput indeedLong
let y :=
  let y :=
    let y := [1, 1, 1, 1, 1];
    1 :: 1 :: 1 :: 1 :: y;
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y :=
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y := 1 :: 1 :: 1 :: 1 :: y;
1 :: 1 :: 1 :: 1 :: y : List Nat
```
```lean +error -keep (name := getThird1)
def getThird (xs : Array α) : α := xs[2]
```
```leanOutput getThird1
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```
```leanOutput getThird1
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```
```lean +error -keep (name := getThird2)
def getThird (xs : Array α) : Option α :=
  if xs.size ≤ 2 then none
  else xs[2]
```
```leanOutput getThird2
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```
```leanOutput getThird2
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```
```lean
def getThird (xs : Array α) : Option α :=
  if h : xs.size ≤ 2 then none
  else xs[2]
```
```lean
inductive Parity : Nat → Type where
  | even (h : Nat) : Parity (h + h)
  | odd (h : Nat) : Parity ((h + h) + 1)

def Nat.parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | n' + 1 =>
    match n'.parity with
    | .even h => .odd h
    | .odd h =>
      have eq : (h + 1) + (h + 1) = (h + h + 1 + 1) :=
        by omega
      eq ▸ .even (h + 1)
```
```lean
def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h
```
```lean -show -keep
-- Check claims about patterns

-- Literals
/-- error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]` -/
#guard_msgs in
def foo (x : String) : String :=
  match x with
  | "abc" => ""
  | r#"hey"# => ""
  | s!"a{x}y" => _
  | _ => default

structure Blah where
  n : Nat
deriving Inhabited

instance : OfNat Blah n where
  ofNat := ⟨n + 1⟩

/--
error: Missing cases:
(Blah.mk (Nat.succ (Nat.succ _)))
(Blah.mk Nat.zero)
-/
#check_msgs in
def abc (n : Blah) : Bool :=
  match n with
  | 0 => true

partial instance : OfNat Blah n where
  ofNat :=
    let rec f (x : Nat) : Blah :=
      match x with
      | 0 => f 99
      | n + 1 => f n
    f n

-- This shows that the partial instance was not unfolded
/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive (instOfNatBlah_1.f 0)
but is expected to have type
  motive n✝
-/
#check_msgs in
def defg (n : Blah) : Bool :=
  match n with
  | 0 => true

/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive (Float.ofScientific 25 true 1)
but is expected to have type
  motive x✝
-/
#check_msgs in
def twoPointFive? : Float → Option Float
  | 2.5 => some 2.5
  | _ => none

/--
info: @Neg.neg.{0} Float instNegFloat
  (@OfScientific.ofScientific.{0} Float instOfScientificFloat (nat_lit 320) Bool.true (nat_lit 1)) : Float
-/
#check_msgs in
set_option pp.all true in
#check -32.0

structure OnlyThreeOrFive where
  val : Nat
  val2 := false
  ok : val = 3 ∨ val = 5 := by rfl


-- Default args are synthesized in patterns too!
/--
error: Tactic `rfl` failed: The left-hand side
  n = 3
is not definitionally equal to the right-hand side
  n = 5

x✝ : OnlyThreeOrFive
n : Nat
⊢ n = 3 ∨ n = 5
-/
#check_msgs in
def ggg : OnlyThreeOrFive → Nat
  | {val := n} => n

/--
error: Missing cases:
(OnlyThreeOrFive.mk _ true _)
-/
#check_msgs in
def hhh : OnlyThreeOrFive → Nat
  | {val := n, ok := p} => n

-- Ellipses don't synth default args in patterns
def ggg' : OnlyThreeOrFive → Nat
  | .mk n .. => n

-- Ellipses do synth default args via tactics, but not exprs, otherwise
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  3 = 3
is not definitionally equal to the right-hand side
  3 = 5

⊢ 3 = 3 ∨ 3 = 5
---
info: { val := 3, val2 := ?m.2647, ok := ⋯ } : OnlyThreeOrFive
-/
#check_msgs in
#check OnlyThreeOrFive.mk 3 ..

/-- info: { val := 3, val2 := ?_, ok := ⋯ } : OnlyThreeOrFive -/
#check_msgs in
set_option pp.mvars.anonymous false in
#check OnlyThreeOrFive.mk 3 (ok := .inl rfl) ..

/--
info: fun y =>
  match
    have this := ⟨y * 3, ⋯⟩;
    this with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), ⋯ => () : Nat → Unit
-/
#check_msgs in
#check fun (y : Nat) => match show {n : Nat// n = y * 3} from ⟨y*3, rfl⟩ with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), rfl => ()

```
```lean -show
variable {α : Type u}
```
```lean
inductive BalancedTree (α : Type u) : Nat → Type u where
  | empty : BalancedTree α 0
  | branch
    (left : BalancedTree α n)
    (val : α)
    (right : BalancedTree α n) :
    BalancedTree α (n + 1)
  | lbranch
    (left : BalancedTree α (n + 1))
    (val : α)
    (right : BalancedTree α n) :
    BalancedTree α (n + 2)
  | rbranch
    (left : BalancedTree α n)
    (val : α)
    (right : BalancedTree α (n + 1)) :
    BalancedTree α (n + 2)
```
```lean -keep (name := fill1) +error
def BalancedTree.filledWith (x : α) (depth : Nat) : BalancedTree α depth := _
```
```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```
```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```
```lean +error (name := fill2)
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  match depth with
  | 0 => _
  | n + 1 => _
```
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```
```lean (name := patfail) +error
def BalancedTree.isPerfectlyBalanced
    (n : Nat) (t : BalancedTree α n) : Bool :=
  match n, t with
  | 0, .empty => true
  | 0, .branch left val right =>
    isPerfectlyBalanced left &&
    isPerfectlyBalanced right
  | _, _ => false
```
```leanOutput patfail
Type mismatch
  left.branch val right
has type
  BalancedTree ?m.54 (?m.51 + 1)
but is expected to have type
  BalancedTree α 0
```
```leanOutput patfail
Type mismatch
  left.branch val right
has type
  BalancedTree ?m.54 (?m.51 + 1)
but is expected to have type
  BalancedTree α 0
```
```lean
def last? (xs : List α) : Except String α :=
  match h : xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```
```lean +error (name := namedHyp)
def last?' (xs : List α) : Except String α :=
  match xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```
```leanOutput namedHyp
simp_all made no progress
```
```leanOutput namedHyp
simp_all made no progress
```
```lean +error (name := noMotive)
#eval
  match 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput noMotive
Invalid match expression: This pattern contains metavariables:
  Eq.refl ?m.76
```
```leanOutput noMotive
Invalid match expression: This pattern contains metavariables:
  Eq.refl ?m.76
```
```lean (name := withMotive)
#eval
  match (motive := (n : Nat) → n = 5 → String) 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput withMotive
"ok"
```
```leanOutput withMotive
"ok"
```
```lean
def f (n : Nat) (p : n = 3) : String :=
  match p with
  | rfl => "ok"
```
```lean (name := fDef)
#print f
```
```leanOutput fDef
def f : (n : Nat) → n = 3 → String :=
fun n p =>
  match 3, p with
  | .(n), ⋯ => "ok"
```
```leanOutput fDef
def f : (n : Nat) → n = 3 → String :=
fun n p =>
  match 3, p with
  | .(n), ⋯ => "ok"
```
```lean -show
variable {α : Type u} (b : Bool) (ifTrue : b = true → α) (ifFalse : b = false → α)
```
```lean +error (name := boolCases1) -keep
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
```leanOutput boolCases1
Application type mismatch: The argument
  h
has type
  b = true
but is expected to have type
  true = true
in the application
  ifTrue h
```
```leanOutput boolCases1
Application type mismatch: The argument
  h
has type
  b = true
but is expected to have type
  true = true
in the application
  ifTrue h
```
```lean
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match (generalizing := false) h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
```lean -show
section
variable {n : Nat}
```
```lean -show
section
variable {k : Nat}
```
```lean +error (name := nonPat)
def nonzero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 + k => true
```
```leanOutput nonPat
Invalid pattern(s): `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 1 k)
```
```leanOutput nonPat
Invalid pattern(s): `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 1 k)
```
```lean
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```
```lean -show
end
```
```lean -show
end
```
```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
```lean
example : isZero = isZero' := rfl
```
```lean (name := isZero)
#print isZero
```
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
```lean (name := isZero')
#print isZero'
```
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
```lean -show
/--
info: match 4 with
| n.succ => true
| x => false : Bool
-/
#check_msgs in
#check 4 matches (n + 1)
```
```lean
example (p1 : x = "Hello") (p2 : x = "world") : False :=
  nomatch p1, p2
```
```lean
example : x = "Hello" → x = "world" → False := nofun
```
```lean
def the (α : Sort u) (x : α) : α := x
```
```lean
#check the String "Hello!"

#check the _ "Hello"
```
```lean (name := byBusted) +error
example (n : Nat) := by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
```leanOutput byBusted
Invalid rewrite argument: Expected an equality or iff proof or definition name, but `ih` is a proof of
  0 ≍ n'
```
```leanOutput byBusted
Invalid rewrite argument: Expected an equality or iff proof or definition name, but `ih` is a proof of
  0 ≍ n'
```
```lean
example (n : Nat) := show 0 + n = n by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
```lean (name := doBusted) +error
example := do
  return 5
```
```leanOutput doBusted
typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.64
```
```leanOutput doBusted
typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.64
```
```lean
example := show StateM String _ from do
  return 5
```